/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Spec.Basic
import ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import PQXDH.ToMathlib
import ToVCVio.CryptoFoundations.SignatureAlg
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.CryptoFoundations.PRF
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.ProgramLogic.Relational.Quantitative

/-!
# PQXDH modeled as a DF'17-style UAKE

Model simplifications
* **Unilateral authentication:** UAKE is unilaterally authenticated. In
  principle, it should be possible to model a protocol in both directions to
  show multilateral authentication. However, we model security only for the
  "Bob authenticates to Alice" direction. This is because UAKE security
  requires explicit authentication, and Alice's authentication to Bob is
  implicit via the adversary being unable to compute the DH output, rather than
  relying on Alice's signature (she signs nothing).
* **SUF-CMA signature (not EUF-CMA):** Since UAKE is a
  transcript-matching-style definition, our security theorems are subject to
  harmless but definition-breaking "no-match" attacks on the signature scheme.
  See Li & Schäge, "No-Match Attacks and Robust Partnering Definitions" (ACM CCS
  2017) for a reference on attacks of this kind.
* **Bob's extra message:** In the PQXDH spec, the exchange ends at Alice's
  first message to Bob, but UAKE requires that the last message be sent by the
  keyed party (Bob). Therefore we add an extra message from Bob under the AEAD
  at the end of the protocol. This would represent the second message in the
  conversation between Alice and Bob.
* **Medium-term secrets as long-term:** The spec describes SPK and PQSPK as
  "changed periodically", but the UAKE security game only allows for permanent
  (via setup) and per-session (via init) keys. We model SPK (and its signature)
  as permanent, along with IK{A|B}.
* **No fallback KEM key:** We do not (currently) model the spec's last-resort
  KEM key (PQSPK). We generate a one-time KEM key (PQOPKᵢ) every time. This is
  a pure simplification, and we plan to extend the model to include the
  last-resort KEM key in the future.

Protocol questions:
* **Key reuse between DH and SignatureAlg:** We assume that Bob's identity key
  contains separate keys for DH exchange and signing. This matches the "no key
  reuse" simplification mentioned in Sec. 4 of the spec that other formal
  analyses required.
* **Separate AEAD key:** The PQXDH spec uses the same KDF output for both
  Alice's AEAD key and the final result of the key exchange, but this seems to
  preclude key indistinguishability. This is because the adversary can try
  using the candidate key to decrypt Alice's message. This will fail for a
  random key (with high likelihood) but succeed for the real key, thus
  distinguishing them. The spec allows KA to be SK or PRF(SK, ·), but both
  variants break key indistinguishability. This could be easily fixed by using
  the KDF output as the key to a PRF that generates **both** SK and KA, but
  the spec **only describes a PRF-derived KA**, which is insufficient. We
  sidestep this and model the final key and Alice's AEAD (and Bob's AEAD key;
  see bullet 3 of "Model simplifications") as separate KDF outputs.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}

inductive Message (G PQPK CT S C IdC IdK : Type) where
  | bundle : PreKeyBundle G PQPK S IdC IdK → Message G PQPK CT S C IdC IdK
  | initial : InitialMessage G CT C IdC IdK → Message G PQPK CT S C IdC IdK
  | confirmation : C → Message G PQPK CT S C IdC IdK
  deriving DecidableEq

def initiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party ProbComp (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiate P p b with
        | some (im, ctx) => pure (.acceptAndSend (.inr (.inl ctx)) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf =>
        match confirm P ctx conf with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr SK) => pure (some (some SK))
    | _ => pure none

def recipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := RecipientParameters F G PQPK PQSK SPK SSK S ⊕ K
  init := fun idn => do
    let opkB ← genOPK P.gen hasOPK
    let pqpkB ← P.pqkem.keygen
    let p : RecipientParameters F G PQPK PQSK SPK SSK S :=
      { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB, spkSigB := idn.spkSigB,
        opkB := opkB, pqpkB := pqpkB }
    let bundle ← publish P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← accept P p im with
        | some ctx => do
            /- DEVIATION FROM SPEC: UAKE requires T to speak last, sending an
              authenticated message if the exchange was accepted. This prevents
              a trivial attack where the attacker simply refrains from sending
              Alice's last message, so that ping-pong is vacuously false. We
              have Bob send the final message of the exchange here in order to
              satisfy this, whereas the spec stops at Bob receiving the
              message. -/
            let conf ← P.aead.encrypt ctx.kb ctx.ad ctx.msg
            pure (.acceptAndSend (.inr ctx.sk) (.confirmation conf) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

def uakeInitiator [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (InitiatorParameters F G SPK Msg)
      (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiator P
  T := recipient P hasOPK

def uakeRecipient [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (RecipientIdentity F G SPK SSK S)
      (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 4
  setup := Prod.swap <$> setup P msg
  U := recipient P hasOPK
  T := initiator P

section CorrectnessLemmas

private lemma probOutput_probComp_evalDist {α : Type} (oa : ProbComp α) (x : α) :
    Pr[= x | ProbCompRuntime.probComp.evalDist oa] = Pr[= x | oa] := by
  rfl

private lemma support_eq_singleton_true_of_evalDist {oa : ProbComp Bool}
    (h : Pr[= true | ProbCompRuntime.probComp.evalDist oa] = 1) :
    support oa = {true} := by
  rw [probOutput_probComp_evalDist, probOutput_eq_one_iff] at h
  exact h.2

private lemma fst_eq_smul_of_mem_support_dhKeygen
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F] {gen : G} {x : G × F}
    (hx : x ∈ support (dhKeygen (F := F) gen)) : x.1 = x.2 • gen := by
  simp only [dhKeygen, mem_support_bind_iff, mem_support_uniformSample, support_pure,
    Set.mem_singleton_iff, true_and] at hx
  obtain ⟨sk, rfl⟩ := hx
  rfl

private lemma verify_eq_true_of_perfectlyComplete
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    {kp : SPK × SSK} (hkp : kp ∈ support P.sig.keygen)
    (m : G ⊕ PQPK) {σ : S} (hσ : σ ∈ support (P.sig.sign kp.1 kp.2 m))
    {b : Bool} (hb : b ∈ support (P.sig.verify kp.1 m σ)) : b = true := by
  have h := support_eq_singleton_true_of_evalDist (hsig m)
  have hmem : b ∈ support (do
      let (pk, sk) ← P.sig.keygen
      let s ← P.sig.sign pk sk m
      P.sig.verify pk m s) := by
    refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
    exact (mem_support_bind_iff _ _ _).mpr ⟨σ, hσ, hb⟩
  rw [h] at hmem
  exact hmem

private lemma decaps_eq_some_of_perfectlyCorrect [DecidableEq SS]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    {kp : PQPK × PQSK} (hkp : kp ∈ support P.pqkem.keygen)
    {cs : CT × SS} (hcs : cs ∈ support (P.pqkem.encaps kp.1))
    {r : Option SS} (hr : r ∈ support (P.pqkem.decaps kp.2 cs.1)) : r = some cs.2 := by
  have h := support_eq_singleton_true_of_evalDist hkem
  have hmem : decide (r = some cs.2) ∈ support P.pqkem.CorrectExp := by
    unfold KEMScheme.CorrectExp
    refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨cs, hcs, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨r, hr, ?_⟩
    simp
  rw [h] at hmem
  simpa using hmem

private lemma aead_decrypt_encrypt_of_perfectlyCorrect [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (k : K) (ad : G × G × PQPK) (m : Msg) {c : C}
    (hc : c ∈ support (P.aead.encrypt k ad m)) :
    P.aead.decrypt k ad c = some m := by
  have h := haead m ad
  rw [probOutput_eq_one_iff] at h
  have hmem : decide (P.aead.decrypt k ad c = some m) ∈
      support (AEAD.CorrectExp P.aead m ad) := by
    unfold AEAD.CorrectExp
    refine (mem_support_bind_iff _ _ _).mpr ⟨k, mem_support_uniformSample K, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨c, hc, ?_⟩
    simp
  rw [h.2] at hmem
  simpa using hmem

private lemma mem_support_initiate
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    {p : InitiatorParameters F G SPK Msg} {bundle : PreKeyBundle G PQPK S IdC IdK}
    {r : Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K)}
    (hpin : bundle.ikB = p.ikB)
    (hok₁ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB),
      b = true)
    (hok₂ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB),
      b = true)
    (hr : r ∈ support (initiate P p bundle)) :
    ∃ ekA ∈ support (dhKeygen (F := F) P.gen),
    ∃ cs ∈ support (P.pqkem.encaps bundle.pqpkB.1),
    ∃ ctxt ∈ support (P.aead.encrypt
        (P.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
          Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).2.1
        (p.ikA.1, p.ikB, bundle.pqpkB.1) p.msg),
      r = some (⟨p.ikA.1, ekA.1, cs.1, bundle.spkB.2, bundle.pqpkB.2,
          Option.map Prod.snd bundle.opkB, ctxt⟩,
        ⟨(P.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
            Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).1,
          (P.kdf (DH p.ikA.2 bundle.spkB.1, DH ekA.2 p.ikB, DH ekA.2 bundle.spkB.1,
            Option.map (fun opk => DH ekA.2 opk.1) bundle.opkB, cs.2)).2.2,
          (p.ikA.1, p.ikB, bundle.pqpkB.1), p.msg⟩) := by
  simp only [initiate, hpin, ne_eq, not_true_eq_false, if_false,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, okSPK, hok, okPQPK, hok', hr⟩ := hr
  obtain rfl := hok₁ _ hok
  obtain rfl := hok₂ _ hok'
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩ := hr
  exact ⟨ekA, hekA, cs, hcs, ctxt, hctxt, rfl⟩

private lemma dh_comm [Field F] [AddCommGroup G] [Module F G] [SampleableType F] {gen : G}
    {x y : G × F} (hx : x ∈ support (dhKeygen (F := F) gen))
    (hy : y ∈ support (dhKeygen (F := F) gen)) : DH x.2 y.1 = DH y.2 x.1 := by
  rw [fst_eq_smul_of_mem_support_dhKeygen hx, fst_eq_smul_of_mem_support_dhKeygen hy,
    DH, DH, smul_smul, smul_smul, mul_comm]

private lemma mem_support_accept
    [Field F] [AddCommGroup G] [Module F G] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    {p : RecipientParameters F G PQPK PQSK SPK SSK S}
    {im : InitialMessage G CT C IdC IdK} {ss : SS} {m₀ : Msg}
    {r : Option (SessionContext G PQPK Msg K)}
    (hid₁ : im.idSPK = P.idEC p.spkB.1)
    (hid₂ : im.idPQPK = P.idKEM p.pqpkB.1)
    (hid₃ : im.idOPK = Option.map (fun opk => P.idEC opk.1) p.opkB)
    (hdec : ∀ o ∈ support (P.pqkem.decaps p.pqpkB.2 im.ct), o = some ss)
    (hdecr : P.aead.decrypt
        (P.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
          Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).2.1
        (im.ikA, p.ikB.1, p.pqpkB.1) im.ctxt = some m₀)
    (hr : r ∈ support (accept P p im)) :
    r = some ⟨(P.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
        Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).1,
      (P.kdf (DH p.spkB.2 im.ikA, DH p.ikB.2 im.ekA, DH p.spkB.2 im.ekA,
        Option.map (fun opk => DH opk.2 im.ekA) p.opkB, ss)).2.2,
      (im.ikA, p.ikB.1, p.pqpkB.1), m₀⟩ := by
  simp only [accept, hid₁, hid₂, hid₃, ne_eq, not_true, or_self, if_false,
    mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
  obtain ⟨_, _, o, ho, hr⟩ := hr
  obtain rfl := hdec _ ho
  simp only [hdecr, support_pure, Set.mem_singleton_iff] at hr
  exact hr

private lemma opkB_mem_of_genOPK {F G : Type}
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    {gen : G} {hasOPK : Bool} {opkB : Option (G × F)}
    (h : opkB ∈ support (genOPK gen hasOPK)) :
    ∀ x ∈ opkB, x ∈ support (dhKeygen (F := F) gen) := by
  unfold genOPK at h
  cases hasOPK with
  | false =>
      simp only [Bool.false_eq_true, if_false, support_pure, Set.mem_singleton_iff] at h
      subst h; simp
  | true =>
      simp only [if_true, support_map, Set.mem_image] at h
      obtain ⟨opk, hopk, rfl⟩ := h
      intro x hx
      simp only [Option.mem_def, Option.some.injEq] at hx
      exact hx ▸ hopk

private lemma run_support_initiator
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (msg : Msg)
    {ikA ikB spkB : G × F} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support (dhKeygen (F := F) P.gen))
    (hikB : ikB ∈ support (dhKeygen (F := F) P.gen))
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support (dhKeygen (F := F) P.gen))
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.1)))
    {uOut tOut : Option (Option K)} {ms : List (Message G PQPK CT S C IdC IdK)}
    (hrun : (uOut, tOut, ms) ∈ support (Party.runHonest (initiator P) (recipient P hasOPK)
      ⟨ikA, ikB.1, sigkB.1, msg⟩ ⟨ikB, sigkB, spkB, spkSigB⟩ (3 + 1))) :
    ∃ k, uOut = some (some k) ∧ tOut = some (some k) := sorry

private lemma run_support_recipient
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (msg : Msg)
    {ikA ikB spkB : G × F} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support (dhKeygen (F := F) P.gen))
    (hikB : ikB ∈ support (dhKeygen (F := F) P.gen))
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support (dhKeygen (F := F) P.gen))
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.1)))
    {uOut tOut : Option (Option K)} {ms : List (Message G PQPK CT S C IdC IdK)}
    (hrun : (uOut, tOut, ms) ∈ support (Party.runHonest (recipient P hasOPK) (initiator P)
      ⟨ikB, sigkB, spkB, spkSigB⟩ ⟨ikA, ikB.1, sigkB.1, msg⟩ (4 + 1))) :
    ∃ k, uOut = some (some k) ∧ tOut = some (some k) := sorry

end CorrectnessLemmas

theorem uakeInitiator_perfectlyCorrect
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) ProbCompRuntime.probComp := sorry

theorem uakeRecipient_perfectlyCorrect
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq IdC] [DecidableEq IdK]
    [DecidableEq K] [DecidableEq SS] [DecidableEq Msg] [SampleableType K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) ProbCompRuntime.probComp := sorry

def _root_.AKE.UAKE.Adversary.OpensAtMost {K UK TK W : Type}
    {proto : UAKE.Scheme ProbComp K UK TK W}
    (A : UAKE.Adversary proto) (q : ℕ) : Prop :=
  (∀ uk w, (A.challenge uk w).IsQueryBoundP (· matches Sum.inr .openT) q) ∧
    (∀ st k, (A.post st k).IsQueryBoundP (· matches Sum.inr .openT) q)

private lemma finalize_true_add_false_eq_one {K UK TK W : Type}
    [SampleableType K] [DecidableEq W] {proto : UAKE.Scheme ProbComp K UK TK W}
    (A : UAKE.Adversary proto) (st : A.State × UAKE.Env proto × TK)
    (cr : UAKE.ChallengeResult proto) (K1 : Option K)
    (hKb : cr.K0 = K1) :
    Pr[= true | UAKE.finalize ProbCompLift.id A st cr true K1] +
      Pr[= true | UAKE.finalize ProbCompLift.id A st cr false K1] = 1 := by
  obtain ⟨aSt, env, tk⟩ := st
  simp only [UAKE.finalize, hKb, ite_self, monadLift_self]
  generalize (simulateQ (UAKE.oracleImpl ProbCompLift.id proto tk) (A.post aSt K1)).run
    { env with challengeDone := true } = run
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, ← ENNReal.tsum_add,
    ← tsum_probOutput_of_liftM_PMF run]
  refine tsum_congr fun x => ?_
  simp only [ProbCompLift.id, MonadHom.id]
  have hsum : Pr[= true | if UAKE.fullPingPong x.2.tSessions cr = true then ($ᵗ Bool)
        else pure (x.1 == true)] +
      Pr[= true | if UAKE.fullPingPong x.2.tSessions cr = true then ($ᵗ Bool)
        else pure (x.1 == false)] = 1 := by
    cases hfpp : UAKE.fullPingPong x.2.tSessions cr
    · cases hx : x.1 <;> simp
    · simp [probOutput_uniformSample, Fintype.card_bool, ENNReal.inv_two_add_inv_two]
  rw [← mul_add, hsum, mul_one]

private lemma finalize_none_half {K UK TK W : Type}
    [SampleableType K] [DecidableEq W] {proto : UAKE.Scheme ProbComp K UK TK W}
    (A : UAKE.Adversary proto) (st : A.State × UAKE.Env proto × TK)
    (cr : UAKE.ChallengeResult proto) (hK0 : cr.K0 = none) :
    Pr[= true | do let b ← $ᵗ Bool; UAKE.finalize ProbCompLift.id A st cr b none] = 1 / 2 := by
  rw [probOutput_bind_uniformBool (fun b => UAKE.finalize ProbCompLift.id A st cr b none) true,
    finalize_true_add_false_eq_one A st cr none hK0]

def kdfPRF [SampleableType SS]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    PRFScheme SS (G × G × G × Option G) (K × K × K) where
  keygen := $ᵗ SS
  eval := fun ss q => P.kdf (q.1, q.2.1, q.2.2.1, q.2.2.2, ss)

def kdfPRFDH [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    PRFScheme F (G × G × Option G × SS) (K × K × K) where
  keygen := $ᵗ F
  eval := fun c q => P.kdf (q.1, q.2.1, c • P.gen, q.2.2.1, q.2.2.2)

private lemma probOutput_bind_if_true_uniformBool {α : Type} (m : ProbComp α) (c : α → Bool) :
    Pr[= true | do let x ← m; if c x then (pure true : ProbComp Bool) else $ᵗ Bool] =
      1 / 2 + Pr[= true | do let x ← m; pure (c x)] / 2 := by
  rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum]
  conv_rhs => rw [show (1 : ℝ≥0∞) / 2 = (∑' x, Pr[= x | m]) / 2 from by
    rw [tsum_probOutput_of_liftM_PMF]]
  simp only [div_eq_mul_inv]
  rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  refine tsum_congr fun x => ?_
  cases hcx : c x
  · simp [probOutput_uniformSample, Fintype.card_bool]
  · have hp : Pr[= x | m] = Pr[= x | m] * 2⁻¹ + Pr[= x | m] * 2⁻¹ := by
      rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]
    simpa [probOutput_uniformSample, Fintype.card_bool] using hp

def initiateIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]
    [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SPK Msg)
    (bundle : PreKeyBundle G PQPK S IdC IdK) :
    ProbComp (Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K)) := do
  if bundle.ikB ≠ p.ikB then return none
  let okSPK ← P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB
  let okPQPK ← P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB
  if !(okSPK && okPQPK) then return none
  let ekA : G × F ← dhKeygen P.gen
  let (CT, _SS) ← P.pqkem.encaps bundle.pqpkB.1
  let (SK, KA, KB) ← ($ᵗ (K × K × K) : ProbComp _)
  let AD := (p.ikA.1, bundle.ikB, bundle.pqpkB.1)
  let ctxt ← P.aead.encrypt KA AD p.msg
  return some ({ ikA := p.ikA.1, ekA := ekA.1, ct := CT, idSPK := bundle.spkB.2,
                 idPQPK := bundle.pqpkB.2, idOPK := bundle.opkB.map Prod.snd, ctxt := ctxt },
    { sk := SK, kb := KB, ad := AD, msg := p.msg })

private lemma initiateIdeal_verify_of_accept [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SPK Msg) (bundle : PreKeyBundle G PQPK S IdC IdK)
    {r : InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K}
    (hr : some r ∈ support (initiateIdeal P p bundle)) :
    true ∈ support (P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB) ∧
      true ∈ support (P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB) := by
  simp only [initiateIdeal] at hr
  split at hr
  · simp at hr
  · rw [mem_support_bind_iff] at hr
    obtain ⟨_, _, hr⟩ := hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨okSPK, hSPK, hr⟩ := hr
    rw [mem_support_bind_iff] at hr
    obtain ⟨okPQPK, hPQPK, hr⟩ := hr
    split at hr
    · simp at hr
    · rename_i hcond
      cases okSPK <;> cases okPQPK <;> simp_all

def initiatorIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K] [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) :
    Party ProbComp (InitiatorParameters F G SPK Msg)
      (Message G PQPK CT S C IdC IdK) (Option K) where
  State := InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K
  init := fun p => pure (.waitForMsg (.inl p))
  step := fun st w => match st, w with
    | .inl p, .bundle b => do
        match ← initiateIdeal P p b with
        | some (im, ctx) => pure (.acceptAndSend (.inr (.inl ctx)) (.initial im) false)
        | none => pure .reject
    | .inr (.inl ctx), .confirmation conf =>
        match confirm P ctx conf with
        | some SK => pure (.complete (.inr (.inr SK)))
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inr (.inr _) => do let SK ← $ᵗ K; pure (some (some SK))
    | _ => pure none

private lemma initiatorIdeal_step_bundle_verify [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (p : InitiatorParameters F G SPK Msg) (b : PreKeyBundle G PQPK S IdC IdK)
    {st' : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K}
    {w' : Message G PQPK CT S C IdC IdK} {done : Bool}
    (hst : Party.StepResult.acceptAndSend st' w' done ∈
      support ((initiatorIdeal P).step (Sum.inl p) (Message.bundle b))) :
    true ∈ support (P.sig.verify p.sigpkB (EncodeEC b.spkB.1) b.spkSigB) ∧
      true ∈ support (P.sig.verify p.sigpkB (EncodeKEM b.pqpkB.1) b.pqpkSigB) := by
  simp only [initiatorIdeal] at hst
  obtain ⟨r, hr, hst⟩ := (mem_support_bind_iff _ _ _).1 hst
  cases r with
  | none => simp at hst
  | some imctx => exact initiateIdeal_verify_of_accept P p b hr

private lemma initiatorIdeal_output_completed [Field F] [AddCommGroup G] [Module F G]
    [SampleableType F] [DecidableEq G] [DecidableEq Msg] [SampleableType K] [Fintype K]
    [Inhabited K]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK)
    (st : InitiatorParameters F G SPK Msg ⊕ SessionContext G PQPK Msg K ⊕ K)
    {y : Option (Option K)} (hy : y ∈ support ((initiatorIdeal P).output st))
    (hjoin : y.join.isSome) :
    ∃ SK, st = Sum.inr (Sum.inr SK) := by
  cases st with
  | inl _ => simp only [initiatorIdeal, support_pure, Set.mem_singleton_iff] at hy
             subst hy; simp at hjoin
  | inr st2 =>
    cases st2 with
    | inl _ => simp only [initiatorIdeal, support_pure, Set.mem_singleton_iff] at hy
               subst hy; simp at hjoin
    | inr SK => exact ⟨SK, rfl⟩

def uakeInitiatorIdeal [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp K (InitiatorParameters F G SPK Msg)
      (RecipientIdentity F G SPK SSK S)
      (Message G PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiatorIdeal P
  T := recipient P hasOPK

def _root_.AKE.UAKE.Adversary.toIdeal
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K]
    [DecidableEq G] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK} {msg : Msg} {hasOPK : Bool}
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Adversary (uakeInitiatorIdeal P msg hasOPK) where
  State := A.State
  challenge := A.challenge
  post := A.post

theorem uakeInitiator_secure_pq
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [SampleableType SS] [DecidableEq SS]
    [Inhabited S] [Inhabited SSK] [Inhabited PQSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εkem εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hkemCorrect : P.pqkem.PerfectlyCorrect ProbCompRuntime.probComp)
    /- DEVIATION FROM SPEC: We require the signature scheme to be SUF-CMA, not
      just EUF-CMA. This is required to avoid (harmless) LS'17-style
      "no-match" attacks because we use a transcript-matching AKE definition. -/
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hkem : ∀ B : P.pqkem.IND_CCA_Adversary,
      P.pqkem.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    /- MODEL SIMPLIFICATION: We model the KDF as a PRF keyed by the KEM secret. -/
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × G × Option G) (K × K × K),
      (kdfPRF P).prfAdvantage D ≤ εkdf) :
    UAKE.advantage ProbCompRuntime.probComp A ≤ 3 * εsig + q * (εkem + 3 * εaead + εkdf) := sorry

theorem uakeInitiator_secure_dh
    [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    [SampleableType K] [Fintype K] [Inhabited K] [Inhabited S] [Inhabited SSK]
    [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
    [DecidableEq SS] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εddh εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    /- DEVIATION FROM SPEC: We require the signature scheme to be SUF-CMA, not
      just EUF-CMA. This is required to avoid (harmless) LS'17-style
      "no-match" attacks because we use a transcript-matching AKE definition. -/
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hddh : ∀ D : DiffieHellman.DDHAdversary F G,
      DiffieHellman.ddhDistAdvantage P.gen D ≤ εddh)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    /- MODEL SIMPLIFICATION: We model the KDF as a PRF. Since we key our KDF
      using DH group elements, we must also assume that the KDF is secure when
      keyed with one of these, rather than a random bit string. -/
    (hkdf : ∀ D : PRFScheme.PRFAdversary (G × G × Option G × SS) (K × K × K),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf) :
    UAKE.advantage ProbCompRuntime.probComp A ≤ εsig + q * (εddh + εaead + εkdf) := sorry

end PQXDH
