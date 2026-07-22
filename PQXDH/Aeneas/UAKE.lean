/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Extracted.Pqxdh
import PQXDH.Spec.Basic
import PQXDH.Spec.UAKE
import ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import ToVCVio.CryptoFoundations.AKE.UAKE.Transport
import PQXDH.HardnessAssumptions.DiffieHellman

/-!
# PQXDH as a UAKE, instantiated with the Aeneas-extracted implementation
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace PQXDH.Aeneas

noncomputable section

instance {α : Type} {n : Aeneas.Std.Usize} [DecidableEq α] :
    DecidableEq (Aeneas.Std.Array α n) :=
  inferInstanceAs (DecidableEq { l : List α // l.length = n.val })

instance : SampleableType Aeneas.Std.U8 :=
  SampleableType.ofEquiv (α := BitVec 8)
    ⟨fun bv => ⟨bv⟩, fun x => x.bv, fun _ => rfl, fun _ => rfl⟩

instance {α : Type} {n : Aeneas.Std.Usize} [SampleableType α] :
    SampleableType (Aeneas.Std.Array α n) :=
  inferInstanceAs (SampleableType (List.Vector α n.val))

instance : Fintype Aeneas.Std.U8 :=
  Fintype.ofEquiv (BitVec 8) ⟨fun bv => ⟨bv⟩, fun x => x.bv, fun _ => rfl, fun _ => rfl⟩

instance {α : Type} {n : Aeneas.Std.Usize} [Fintype α] :
    Fintype (Aeneas.Std.Array α n) :=
  inferInstanceAs (Fintype (List.Vector α n.val))

abbrev Bytes (n : Aeneas.Std.Usize) : Type := Aeneas.Std.Array Aeneas.Std.U8 n

abbrev ECKey : Type := Bytes 32#usize

abbrev PQPK : Type := Bytes 1568#usize

abbrev PQSK : Type := Bytes 3168#usize

abbrev CT : Type := Bytes 1569#usize

abbrev SS : Type := Bytes 32#usize

abbrev Key : Type := Bytes 32#usize

abbrev Coins : Type := Bytes 32#usize

def getOk {α : Type} [Inhabited α] : Aeneas.Std.Result α → α
  | .ok x => x
  | _ => default

def deriveKeys (dh1 dh2 dh3 : ECKey) (dh4 : Option ECKey) (ss : SS) :
    Aeneas.Std.Result (Key × Key × Key) := do
  let okm ← match dh4 with
    | none => do
        let secretInput ← pqxdh.pqxdh_secret_input dh1 dh2 dh3 ss
        let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice secretInput)
        let s1 ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice pqxdh.PQXDH_LABEL)
        pqxdh.hkdf_sha256_derive s s1
    | some dh4 => do
        let secretInput ← pqxdh.pqxdh_secret_input_with_opk dh1 dh2 dh3 dh4 ss
        let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice secretInput)
        let s1 ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice pqxdh.PQXDH_LABEL)
        pqxdh.hkdf_sha256_derive s s1
  pqxdh.derive_split okm

def DeriveKeysTotal : Prop :=
  ∀ (dh1 dh2 dh3 : ECKey) (dh4 : Option ECKey) (ss : SS),
    ∃ ks, deriveKeys dh1 dh2 dh3 dh4 ss = .ok ks

variable {SPK SSK S C Msg IdC IdK : Type}

structure Parameters (SPK SSK S C Msg IdC IdK : Type) where
  ecKeygen : ProbComp pqxdh.KeyPair
  pqKeygen : ProbComp (PQPK × PQSK)
  encapsCoins : ProbComp Coins
  sig : SignatureAlg ProbComp (ECKey ⊕ PQPK) SPK SSK S
  aead : AEAD.Scheme ProbComp Msg Key (ECKey × ECKey × PQPK) C
  idEC : ECKey → IdC
  idKEM : PQPK → IdK

structure InitiatorParameters (SPK Msg : Type) where
  ikA : pqxdh.KeyPair
  ikB : ECKey
  sigpkB : SPK
  msg : Msg

structure RecipientIdentity (SPK SSK S : Type) where
  ikB : pqxdh.KeyPair
  sigkB : SPK × SSK
  spkB : pqxdh.KeyPair
  spkSigB : S

structure RecipientParameters (SPK SSK S : Type) where
  ikB : pqxdh.KeyPair
  sigkB : SPK × SSK
  spkB : pqxdh.KeyPair
  spkSigB : S
  opkB : Option pqxdh.KeyPair
  pqpkB : PQPK × PQSK

def pqkem (P : Parameters SPK SSK S C Msg IdC IdK) :
    KEMScheme ProbComp SS PQPK PQSK CT where
  keygen := P.pqKeygen
  encaps := fun pk => do
    let coins ← P.encapsCoins
    match pqxdh.mlkem_encapsulate pk coins with
    | .ok (ss, ct) => return (ct, ss)
    | _ => return default
  decaps := fun sk ct =>
    match pqxdh.mlkem_decapsulate sk ct with
    | .ok ss => return some ss
    | _ => return none

def AgreeComm (P : Parameters SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ kp₁ ∈ support P.ecKeygen, ∀ kp₂ ∈ support P.ecKeygen,
    pqxdh.x25519_agree kp₁.private_key kp₂.public_key
      = pqxdh.x25519_agree kp₂.private_key kp₁.public_key

def AgreeTotal (P : Parameters SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ kp₁ ∈ support P.ecKeygen, ∀ kp₂ ∈ support P.ecKeygen,
    ∃ z, pqxdh.x25519_agree kp₁.private_key kp₂.public_key = .ok z

def EncapsTotal (P : Parameters SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ kp ∈ support P.pqKeygen, ∀ coins ∈ support P.encapsCoins,
    ∃ r, pqxdh.mlkem_encapsulate kp.1 coins = .ok r

def kdfPRF : PRFScheme SS (ECKey × ECKey × ECKey × Option ECKey) (Key × Key × Key) where
  keygen := $ᵗ SS
  eval := fun ss q => getOk (deriveKeys q.1 q.2.1 q.2.2.1 q.2.2.2 ss)

def kdfPRFDH (P : Parameters SPK SSK S C Msg IdC IdK) :
    PRFScheme pqxdh.KeyPair (ECKey × ECKey × Option ECKey × SS) (Key × Key × Key) where
  keygen := P.ecKeygen
  eval := fun kp q => getOk (deriveKeys q.1 q.2.1 kp.public_key q.2.2.1 q.2.2.2)

def x25519DH (kp : pqxdh.KeyPair) (pk : ECKey) : ECKey :=
  getOk (pqxdh.x25519_agree kp.private_key pk)

def genOPK (keygen : ProbComp pqxdh.KeyPair) (hasOPK : Bool) :
    ProbComp (Option pqxdh.KeyPair) :=
  if hasOPK then some <$> keygen else pure none

def setup (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) :
    ProbComp (InitiatorParameters SPK Msg × RecipientIdentity SPK SSK S) := do
  let ikA ← P.ecKeygen
  let ikB ← P.ecKeygen
  let sigkB ← P.sig.keygen
  let spkB ← P.ecKeygen
  let spkSigB ← P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)
  return ({ ikA := ikA, ikB := ikB.public_key, sigpkB := sigkB.1, msg := msg },
    { ikB := ikB, sigkB := sigkB, spkB := spkB, spkSigB := spkSigB })

def publish (P : Parameters SPK SSK S C Msg IdC IdK)
    (p : RecipientParameters SPK SSK S) :
    ProbComp (PreKeyBundle ECKey PQPK S IdC IdK) := do
  let pqpkSigB ← P.sig.sign p.sigkB.1 p.sigkB.2 (EncodeKEM p.pqpkB.1)
  return { ikB := p.ikB.public_key
           spkB := (p.spkB.public_key, P.idEC p.spkB.public_key)
           spkSigB := p.spkSigB
           pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
           pqpkSigB := pqpkSigB
           opkB := p.opkB.map fun opk => (opk.public_key, P.idEC opk.public_key) }

def initiate (P : Parameters SPK SSK S C Msg IdC IdK)
    (p : InitiatorParameters SPK Msg)
    (bundle : PreKeyBundle ECKey PQPK S IdC IdK) :
    ProbComp (Option (InitialMessage ECKey CT C IdC IdK ×
      SessionContext ECKey PQPK Msg Key)) := do
  if bundle.ikB ≠ p.ikB then return none
  let okSPK ← P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB
  let okPQPK ← P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB
  if !(okSPK && okPQPK) then return none
  let ekA ← P.ecKeygen
  let coins ← P.encapsCoins
  match pqxdh.pqxdh_initiate
      { our_identity_key_pair := p.ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := bundle.ikB
        their_signed_pre_key := bundle.spkB.1
        their_one_time_pre_key := bundle.opkB.map Prod.fst
        their_kyber_pre_key := bundle.pqpkB.1 } coins with
  | .ok agreement =>
      let SK := agreement.keys.root_key
      let KA := agreement.keys.chain_key
      let KB := agreement.keys.pqr_key
      let AD := (p.ikA.public_key, bundle.ikB, bundle.pqpkB.1)
      let ctxt ← P.aead.encrypt KA AD p.msg
      return some ({ ikA := p.ikA.public_key
                     ekA := ekA.public_key
                     ct := agreement.kyber_ciphertext
                     idSPK := bundle.spkB.2
                     idPQPK := bundle.pqpkB.2
                     idOPK := bundle.opkB.map Prod.snd
                     ctxt := ctxt },
        { sk := SK, kb := KB, ad := AD, msg := p.msg })
  | _ => return none

def accept [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (p : RecipientParameters SPK SSK S)
    (msg : InitialMessage ECKey CT C IdC IdK) :
    ProbComp (Option (SessionContext ECKey PQPK Msg Key)) := do
  if msg.idSPK ≠ P.idEC p.spkB.public_key ∨ msg.idPQPK ≠ P.idKEM p.pqpkB.1 ∨
      msg.idOPK ≠ p.opkB.map (fun opk => P.idEC opk.public_key) then return none
  match pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_secret_key := p.pqpkB.2
        their_identity_key := msg.ikA
        their_ephemeral_key := msg.ekA
        their_kyber_ciphertext := msg.ct } with
  | .ok (some keys) =>
      let AD := (msg.ikA, p.ikB.public_key, p.pqpkB.1)
      match P.aead.decrypt keys.chain_key AD msg.ctxt with
      | some m =>
          return some { sk := keys.root_key, kb := keys.pqr_key, ad := AD, msg := m }
      | none => return none
  | _ => return none

def confirm [DecidableEq Msg] (P : Parameters SPK SSK S C Msg IdC IdK)
    (ctx : SessionContext ECKey PQPK Msg Key) (conf : C) : Option Key :=
  if P.aead.decrypt ctx.kb ctx.ad conf = some ctx.msg then some ctx.sk
  else none

def initiator [DecidableEq Msg] (P : Parameters SPK SSK S C Msg IdC IdK) :
    Party ProbComp (InitiatorParameters SPK Msg)
      (Message ECKey PQPK CT S C IdC IdK) (Option Key) where
  State := InitiatorParameters SPK Msg ⊕ SessionContext ECKey PQPK Msg Key ⊕ Key
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

def recipient [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity SPK SSK S)
      (Message ECKey PQPK CT S C IdC IdK) (Option Key) where
  State := RecipientParameters SPK SSK S ⊕ Key
  init := fun idn => do
    let opkB ← genOPK P.ecKeygen hasOPK
    let pqpkB ← P.pqKeygen
    let p : RecipientParameters SPK SSK S :=
      { ikB := idn.ikB, sigkB := idn.sigkB, spkB := idn.spkB, spkSigB := idn.spkSigB,
        opkB := opkB, pqpkB := pqpkB }
    let bundle ← publish P p
    pure (.speakFirst (.inl p) (.bundle bundle))
  step := fun st w => match st, w with
    | .inl p, .initial im => do
        match ← accept P p im with
        | some ctx => do
            let conf ← P.aead.encrypt ctx.kb ctx.ad ctx.msg
            pure (.acceptAndSend (.inr ctx.sk) (.confirmation conf) true)
        | none => pure .reject
    | _, _ => pure .reject
  output := fun st => match st with
    | .inl _ => pure none
    | .inr SK => pure (some (some SK))

def uakeInitiator [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp Key (InitiatorParameters SPK Msg)
      (RecipientIdentity SPK SSK S)
      (Message ECKey PQPK CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiator P
  T := recipient P hasOPK

def uakeRecipient [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp Key (RecipientIdentity SPK SSK S)
      (InitiatorParameters SPK Msg)
      (Message ECKey PQPK CT S C IdC IdK) where
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

private lemma verify_eq_true_of_perfectlyComplete
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    {kp : SPK × SSK} (hkp : kp ∈ support P.sig.keygen)
    (m : ECKey ⊕ PQPK) {σ : S} (hσ : σ ∈ support (P.sig.sign kp.1 kp.2 m))
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

private lemma mlkem_decapsulate_eq_ok
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    {kp : PQPK × PQSK} (hkp : kp ∈ support P.pqKeygen)
    {coins : Coins} (hcoins : coins ∈ support P.encapsCoins)
    {ss : SS} {ct : CT} (henc : pqxdh.mlkem_encapsulate kp.1 coins = .ok (ss, ct)) :
    pqxdh.mlkem_decapsulate kp.2 ct = .ok ss := by
  have h := support_eq_singleton_true_of_evalDist hkem
  have hct : (ct, ss) ∈ support ((pqkem P).encaps kp.1) := by
    simp only [pqkem, mem_support_bind_iff]
    exact ⟨coins, hcoins, by simp [henc]⟩
  have key : ∀ r ∈ support ((pqkem P).decaps kp.2 ct), r = some ss := by
    intro r hr
    have hmem : decide (r = some ss) ∈ support ((pqkem P).CorrectExp) := by
      unfold KEMScheme.CorrectExp
      refine (mem_support_bind_iff _ _ _).mpr ⟨kp, hkp, ?_⟩
      refine (mem_support_bind_iff _ _ _).mpr ⟨(ct, ss), hct, ?_⟩
      refine (mem_support_bind_iff _ _ _).mpr ⟨r, hr, ?_⟩
      simp
    rw [h] at hmem
    simpa using hmem
  cases hdec : pqxdh.mlkem_decapsulate kp.2 ct with
  | ok ss' =>
      have := key (some ss') (by simp [pqkem, hdec])
      simp only [Option.some.injEq] at this
      rw [this]
  | fail e =>
      have := key none (by simp [pqkem, hdec])
      simp at this
  | div =>
      have := key none (by simp [pqkem, hdec])
      simp at this

private lemma aead_decrypt_encrypt_of_perfectlyCorrect [DecidableEq Msg]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (k : Key) (ad : ECKey × ECKey × PQPK) (m : Msg) {c : C}
    (hc : c ∈ support (P.aead.encrypt k ad m)) :
    P.aead.decrypt k ad c = some m := by
  have h := haead m ad
  rw [probOutput_eq_one_iff] at h
  have hmem : decide (P.aead.decrypt k ad c = some m) ∈
      support (AEAD.CorrectExp P.aead m ad) := by
    unfold AEAD.CorrectExp
    refine (mem_support_bind_iff _ _ _).mpr ⟨k, mem_support_uniformSample Key, ?_⟩
    refine (mem_support_bind_iff _ _ _).mpr ⟨c, hc, ?_⟩
    simp
  rw [h.2] at hmem
  simpa using hmem

private lemma opkB_mem_of_genOPK {keygen : ProbComp pqxdh.KeyPair} {hasOPK : Bool}
    {opkB : Option pqxdh.KeyPair}
    (h : opkB ∈ support (genOPK keygen hasOPK)) :
    ∀ x ∈ opkB, x ∈ support keygen := by
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

private lemma pqxdh_accept_eq_of_initiate_eq_ok
    (ikA ekA ikB spkB : pqxdh.KeyPair) (opkB : Option pqxdh.KeyPair)
    (pqpk : PQPK) (pqsk : PQSK) (coins : Coins) (ag : pqxdh.InitiatorAgreement)
    (hdh1 : pqxdh.x25519_agree spkB.private_key ikA.public_key
      = pqxdh.x25519_agree ikA.private_key spkB.public_key)
    (hdh2 : pqxdh.x25519_agree ikB.private_key ekA.public_key
      = pqxdh.x25519_agree ekA.private_key ikB.public_key)
    (hdh3 : pqxdh.x25519_agree spkB.private_key ekA.public_key
      = pqxdh.x25519_agree ekA.private_key spkB.public_key)
    (hdh4 : ∀ opk ∈ opkB, pqxdh.x25519_agree opk.private_key ekA.public_key
      = pqxdh.x25519_agree ekA.private_key opk.public_key)
    (hkem : ∀ ss ct, pqxdh.mlkem_encapsulate pqpk coins = .ok (ss, ct) →
      pqxdh.mlkem_decapsulate pqsk ct = .ok ss)
    (hcanon : pqxdh.ec_is_canonical ekA.public_key = .ok true)
    (hI : pqxdh.pqxdh_initiate
      { our_identity_key_pair := ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := ikB.public_key
        their_signed_pre_key := spkB.public_key
        their_one_time_pre_key := opkB.map pqxdh.KeyPair.public_key
        their_kyber_pre_key := pqpk } coins = .ok ag) :
    pqxdh.pqxdh_accept
      { our_identity_key_pair := ikB
        our_signed_pre_key_pair := spkB
        our_one_time_pre_key_pair := opkB
        our_kyber_secret_key := pqsk
        their_identity_key := ikA.public_key
        their_ephemeral_key := ekA.public_key
        their_kyber_ciphertext := ag.kyber_ciphertext } = .ok (some ag.keys) := by
  unfold pqxdh.pqxdh_initiate at hI
  unfold pqxdh.pqxdh_accept
  simp only [Aeneas.Std.lift] at hI ⊢
  cases h1 : pqxdh.x25519_agree ikA.private_key spkB.public_key with
  | fail e => simp [h1] at hI
  | div => simp [h1] at hI
  | ok dh1 =>
  cases h2 : pqxdh.x25519_agree ekA.private_key ikB.public_key with
  | fail e => simp [h1, h2] at hI
  | div => simp [h1, h2] at hI
  | ok dh2 =>
  cases h3 : pqxdh.x25519_agree ekA.private_key spkB.public_key with
  | fail e => simp [h1, h2, h3] at hI
  | div => simp [h1, h2, h3] at hI
  | ok dh3 =>
  cases henc : pqxdh.mlkem_encapsulate pqpk coins with
  | fail e => simp [h1, h2, h3, henc] at hI
  | div => simp [h1, h2, h3, henc] at hI
  | ok ssct =>
  obtain ⟨ss, ct⟩ := ssct
  have hdec := hkem ss ct henc
  cases opkB with
  | none =>
      cases hsi : pqxdh.pqxdh_secret_input dh1 dh2 dh3 ss with
      | fail e => simp [h1, h2, h3, henc, hsi] at hI
      | div => simp [h1, h2, h3, henc, hsi] at hI
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [h1, h2, h3, henc, hsi, hokm] at hI
      | div => simp [h1, h2, h3, henc, hsi, hokm] at hI
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [h1, h2, h3, henc, hsi, hokm, hsplit] at hI
      | div => simp [h1, h2, h3, henc, hsi, hokm, hsplit] at hI
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp [h1, h2, h3, henc, hsi, hokm, hsplit] at hI
      subst hI
      simp [hcanon, hdh1, hdh2, hdh3, h1, h2, h3, hdec, hsi, hokm, hsplit]
  | some opk =>
      cases h4 : pqxdh.x25519_agree ekA.private_key opk.public_key with
      | fail e => simp [h1, h2, h3, henc, h4] at hI
      | div => simp [h1, h2, h3, henc, h4] at hI
      | ok dh4 =>
      cases hsi : pqxdh.pqxdh_secret_input_with_opk dh1 dh2 dh3 dh4 ss with
      | fail e => simp [h1, h2, h3, henc, h4, hsi] at hI
      | div => simp [h1, h2, h3, henc, h4, hsi] at hI
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [h1, h2, h3, henc, h4, hsi, hokm] at hI
      | div => simp [h1, h2, h3, henc, h4, hsi, hokm] at hI
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [h1, h2, h3, henc, h4, hsi, hokm, hsplit] at hI
      | div => simp [h1, h2, h3, henc, h4, hsi, hokm, hsplit] at hI
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp [h1, h2, h3, henc, h4, hsi, hokm, hsplit] at hI
      subst hI
      simp [hcanon, hdh1, hdh2, hdh3, hdh4 opk rfl, h1, h2, h3, h4, hdec, hsi, hokm, hsplit]

private lemma mem_support_initiate
    (P : Parameters SPK SSK S C Msg IdC IdK)
    {p : InitiatorParameters SPK Msg} {bundle : PreKeyBundle ECKey PQPK S IdC IdK}
    {r : Option (InitialMessage ECKey CT C IdC IdK × SessionContext ECKey PQPK Msg Key)}
    (hpin : bundle.ikB = p.ikB)
    (hok₁ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB),
      b = true)
    (hok₂ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB),
      b = true)
    (hr : r ∈ support (initiate P p bundle)) :
    r = none ∨
      ∃ ekA ∈ support P.ecKeygen, ∃ coins ∈ support P.encapsCoins,
      ∃ ag : pqxdh.InitiatorAgreement,
        pqxdh.pqxdh_initiate
          { our_identity_key_pair := p.ikA
            our_ephemeral_key_pair := ekA
            their_identity_key := p.ikB
            their_signed_pre_key := bundle.spkB.1
            their_one_time_pre_key := bundle.opkB.map Prod.fst
            their_kyber_pre_key := bundle.pqpkB.1 } coins = .ok ag ∧
      ∃ ctxt ∈ support (P.aead.encrypt ag.keys.chain_key
          (p.ikA.public_key, p.ikB, bundle.pqpkB.1) p.msg),
        r = some (⟨p.ikA.public_key, ekA.public_key, ag.kyber_ciphertext,
            bundle.spkB.2, bundle.pqpkB.2, bundle.opkB.map Prod.snd, ctxt⟩,
          ⟨ag.keys.root_key, ag.keys.pqr_key,
            (p.ikA.public_key, p.ikB, bundle.pqpkB.1), p.msg⟩) := by
  simp only [initiate, hpin, ne_eq, not_true_eq_false, if_false,
    mem_support_bind_iff] at hr
  obtain ⟨_, _, okSPK, hok, okPQPK, hok', hr⟩ := hr
  obtain rfl := hok₁ _ hok
  obtain rfl := hok₂ _ hok'
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false,
    mem_support_bind_iff] at hr
  obtain ⟨_, _, ekA, hekA, coins, hcoins, hr⟩ := hr
  cases hI : pqxdh.pqxdh_initiate
      { our_identity_key_pair := p.ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := p.ikB
        their_signed_pre_key := bundle.spkB.1
        their_one_time_pre_key := bundle.opkB.map Prod.fst
        their_kyber_pre_key := bundle.pqpkB.1 } coins with
  | ok ag =>
      rw [hI] at hr
      simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
      obtain ⟨ctxt, hctxt, rfl⟩ := hr
      exact Or.inr ⟨ekA, hekA, coins, hcoins, ag, hI, ctxt, hctxt, rfl⟩
  | fail e =>
      rw [hI] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      exact Or.inl hr
  | div =>
      rw [hI] at hr
      simp only [support_pure, Set.mem_singleton_iff] at hr
      exact Or.inl hr

private lemma accept_eq_pure_some
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    {p : RecipientParameters SPK SSK S} {im : InitialMessage ECKey CT C IdC IdK}
    {keys : pqxdh.HandshakeKeys} {m₀ : Msg}
    (hid₁ : im.idSPK = P.idEC p.spkB.public_key)
    (hid₂ : im.idPQPK = P.idKEM p.pqpkB.1)
    (hid₃ : im.idOPK = p.opkB.map (fun opk => P.idEC opk.public_key))
    (hacc : pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_secret_key := p.pqpkB.2
        their_identity_key := im.ikA
        their_ephemeral_key := im.ekA
        their_kyber_ciphertext := im.ct } = .ok (some keys))
    (hdec : P.aead.decrypt keys.chain_key (im.ikA, p.ikB.public_key, p.pqpkB.1) im.ctxt
      = some m₀) :
    accept P p im = pure (some ⟨keys.root_key, keys.pqr_key,
      (im.ikA, p.ikB.public_key, p.pqpkB.1), m₀⟩) := by
  simp [accept, hid₁, hid₂, hid₃, hacc, hdec]

private lemma accept_eq_pure_none
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    {p : RecipientParameters SPK SSK S} {im : InitialMessage ECKey CT C IdC IdK}
    (hacc : ∀ keys, pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_secret_key := p.pqpkB.2
        their_identity_key := im.ikA
        their_ephemeral_key := im.ekA
        their_kyber_ciphertext := im.ct } ≠ .ok (some keys)) :
    accept P p im = pure none := by
  cases hr : pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_secret_key := p.pqpkB.2
        their_identity_key := im.ikA
        their_ephemeral_key := im.ekA
        their_kyber_ciphertext := im.ct } with
  | ok o =>
      cases o with
      | none => simp [accept, hr]
      | some keys => exact absurd hr (hacc keys)
  | fail e => simp [accept, hr]
  | div => simp [accept, hr]

private lemma pqxdh_accept_ne_ok_some
    {rp : pqxdh.RecipientParameters} {res : Aeneas.Std.Result Bool}
    (hc : pqxdh.ec_is_canonical rp.their_ephemeral_key = res) (hres : res ≠ .ok true) :
    ∀ keys, pqxdh.pqxdh_accept rp ≠ .ok (some keys) := by
  intro keys h
  unfold pqxdh.pqxdh_accept at h
  rw [hc] at h
  cases res with
  | ok b =>
      cases b with
      | true => exact hres rfl
      | false => simp at h
  | fail e => simp at h
  | div => simp at h

private lemma run_support_initiator
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P)
    (msg : Msg)
    {ikA ikB spkB : pqxdh.KeyPair} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support P.ecKeygen)
    (hikB : ikB ∈ support P.ecKeygen)
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support P.ecKeygen)
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)))
    {uOut tOut : Option (Option Key)}
    (hrun : (uOut, tOut) ∈ support (Party.runHonest (initiator P) (recipient P hasOPK)
      ⟨ikA, ikB.public_key, sigkB.1, msg⟩ ⟨ikB, sigkB, spkB, spkSigB⟩ (3 + 1))) :
    uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join := by
  simp only [Party.runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, rfl, qInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₂, hσ₂, rfl⟩ := hbundle
  simp only [Party.InitResult.opening, Party.InitResult.state, mem_support_bind_iff] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [Party.runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  rcases mem_support_initiate P rfl
      (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hspkSigB hb)
      (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₂ hb) hir with
    rfl | ⟨ekA, hekA, coins, hcoins, ag, hI, ctxt, hctxt, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
    obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
    simp
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    dsimp only at hctxt hy
    simp only [mem_support_bind_iff] at hy
    obtain ⟨sr, ⟨ar, har, hsr⟩, hy⟩ := hy
    have hmap : Option.map Prod.fst
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map pqxdh.KeyPair.public_key opkB := by
      cases opkB <;> rfl
    rw [hmap] at hI
    have hidOPK : Option.map Prod.snd
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map (fun opk => P.idEC opk.public_key) opkB := by
      cases opkB <;> rfl
    cases hc : pqxdh.ec_is_canonical ekA.public_key with
    | ok b =>
      cases b with
      | true =>
        have hacc := pqxdh_accept_eq_of_initiate_eq_ok ikA ekA ikB spkB opkB
          pqpkB.1 pqpkB.2 coins ag
          (hdh spkB hspkB ikA hikA) (hdh ikB hikB ekA hekA) (hdh spkB hspkB ekA hekA)
          (fun opk hopk => hdh opk (hopkB opk hopk) ekA hekA)
          (fun ss ct h => mlkem_decapsulate_eq_ok P hkem hpqpkB hcoins h) hc hI
        have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
        rw [accept_eq_pure_some P rfl rfl hidOPK hacc hdecA] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsr
        obtain ⟨conf, hconf, rfl⟩ := hsr
        have hconfirm := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hconf
        simp only [confirm, hconfirm, reduceIte, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hy
        obtain ⟨x, rfl, hy⟩ := hy
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp
      | false =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp
    | fail e =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp
    | div =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp

private lemma run_support_recipient
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P)
    (msg : Msg)
    {ikA ikB spkB : pqxdh.KeyPair} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support P.ecKeygen)
    (hikB : ikB ∈ support P.ecKeygen)
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support P.ecKeygen)
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)))
    {uOut tOut : Option (Option Key)}
    (hrun : (uOut, tOut) ∈ support (Party.runHonest (recipient P hasOPK) (initiator P)
      ⟨ikB, sigkB, spkB, spkSigB⟩ ⟨ikA, ikB.public_key, sigkB.1, msg⟩ (4 + 1))) :
    uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join := by
  simp only [Party.runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, qInit, rfl, hrun⟩ := hrun
  have hopkB := opkB_mem_of_genOPK hopkB_mem
  simp only [publish, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hbundle
  obtain ⟨σ₂, hσ₂, rfl⟩ := hbundle
  simp only [Party.InitResult.opening, Party.InitResult.state, mem_support_bind_iff] at hrun
  obtain ⟨y, hy, hout⟩ := hrun
  simp only [Party.runHonestLoop, mem_support_bind_iff] at hy
  obtain ⟨r, ⟨ir, hir, hr⟩, hy⟩ := hy
  rcases mem_support_initiate P rfl
      (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hspkSigB hb)
      (fun b hb => verify_eq_true_of_perfectlyComplete P hsig hsigkB _ hσ₂ hb) hir with
    rfl | ⟨ekA, hekA, coins, hcoins, ag, hI, ctxt, hctxt, rfl⟩
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
    obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
    simp
  · simp only [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    dsimp only at hctxt hy
    simp only [mem_support_bind_iff] at hy
    obtain ⟨sr, ⟨ar, har, hsr⟩, hy⟩ := hy
    have hmap : Option.map Prod.fst
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map pqxdh.KeyPair.public_key opkB := by
      cases opkB <;> rfl
    rw [hmap] at hI
    have hidOPK : Option.map Prod.snd
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map (fun opk => P.idEC opk.public_key) opkB := by
      cases opkB <;> rfl
    cases hc : pqxdh.ec_is_canonical ekA.public_key with
    | ok b =>
      cases b with
      | true =>
        have hacc := pqxdh_accept_eq_of_initiate_eq_ok ikA ekA ikB spkB opkB
          pqpkB.1 pqpkB.2 coins ag
          (hdh spkB hspkB ikA hikA) (hdh ikB hikB ekA hekA) (hdh spkB hspkB ekA hekA)
          (fun opk hopk => hdh opk (hopkB opk hopk) ekA hekA)
          (fun ss ct h => mlkem_decapsulate_eq_ok P hkem hpqpkB hcoins h) hc hI
        have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
        rw [accept_eq_pure_some P rfl rfl hidOPK hacc hdecA] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsr
        obtain ⟨conf, hconf, rfl⟩ := hsr
        have hconfirm := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hconf
        simp only [confirm, hconfirm, reduceIte, mem_support_bind_iff, support_pure,
          Set.mem_singleton_iff] at hy
        obtain ⟨x, rfl, hy⟩ := hy
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp
      | false =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp
    | fail e =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp
    | div =>
        rw [accept_eq_pure_none P (pqxdh_accept_ne_ok_some hc (by simp))] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [support_pure, Set.mem_singleton_iff] at hsr
        subst hsr
        simp only [support_pure, Set.mem_singleton_iff] at hy
        subst hy
        simp only [support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hout
        obtain ⟨pOut, rfl, qOut, rfl, rfl, rfl⟩ := hout
        simp

end CorrectnessLemmas

theorem uakeInitiator_perfectlyCorrect
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) := by
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact probFailure_of_liftM_PMF _
  intro b hb
  simp only [UAKE.CorrectExp, uakeInitiator, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, hrun, rfl⟩ := hb
  suffices h : uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join by
    simpa using h
  simp only [setup, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsetup
  obtain ⟨ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, spkSigB, hspkSigB, huk, htk⟩ := hsetup
  subst huk htk
  exact run_support_initiator P hasOPK hsig hkem haead hdh msg hikA hikB hsigkB hspkB
    hspkSigB hrun

theorem uakeRecipient_perfectlyCorrect
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) := by
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact probFailure_of_liftM_PMF _
  intro b hb
  simp only [UAKE.CorrectExp, uakeRecipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, hrun, rfl⟩ := hb
  suffices h : uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join by
    simpa using h
  simp only [setup, support_map, Set.mem_image, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hsetup
  obtain ⟨x, ⟨ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, spkSigB, hspkSigB, rfl⟩,
    hswap⟩ := hsetup
  simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hswap
  obtain ⟨huk, htk⟩ := hswap
  subst huk htk
  exact run_support_recipient P hasOPK hsig hkem haead hdh msg hikA hikB hsigkB hspkB
    hspkSigB hrun

section Security

def specParams (P : Parameters SPK SSK S C Msg IdC IdK) (F : Type) (gen : ECKey) :
    _root_.PQXDH.Parameters F ECKey SS PQPK PQSK CT SPK SSK S C Msg Key IdC IdK where
  gen := gen
  pqkem := pqkem P
  sig := P.sig
  aead := P.aead
  kdf := fun km => getOk (deriveKeys km.1 km.2.1 km.2.2.1 km.2.2.2.1 km.2.2.2.2)
  idEC := P.idEC
  idKEM := P.idKEM

variable {F : Type}

def kpOfPair (privEnc : F → Bytes 32#usize) (p : ECKey × F) : pqxdh.KeyPair where
  private_key := privEnc p.2
  public_key := p.1

def ukOfSpec (privEnc : F → Bytes 32#usize)
    (uk : _root_.PQXDH.InitiatorParameters F ECKey SPK Msg) :
    InitiatorParameters SPK Msg where
  ikA := kpOfPair privEnc uk.ikA
  ikB := uk.ikB
  sigpkB := uk.sigpkB
  msg := uk.msg

def tkOfSpec (privEnc : F → Bytes 32#usize)
    (tk : _root_.PQXDH.RecipientIdentity F ECKey SPK SSK S) :
    RecipientIdentity SPK SSK S where
  ikB := kpOfPair privEnc tk.ikB
  sigkB := tk.sigkB
  spkB := kpOfPair privEnc tk.spkB
  spkSigB := tk.spkSigB

def rpOfSpec (privEnc : F → Bytes 32#usize)
    (rp : _root_.PQXDH.RecipientParameters F ECKey PQPK PQSK SPK SSK S) :
    RecipientParameters SPK SSK S where
  ikB := kpOfPair privEnc rp.ikB
  sigkB := rp.sigkB
  spkB := kpOfPair privEnc rp.spkB
  spkSigB := rp.spkSigB
  opkB := rp.opkB.map (kpOfPair privEnc)
  pqpkB := rp.pqpkB

structure ECGroupModel [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey]
    (P : Parameters SPK SSK S C Msg IdC IdK) (gen : ECKey) (privEnc : F → Bytes 32#usize) :
    Prop where
  keygen_eq : P.ecKeygen = kpOfPair privEnc <$> _root_.PQXDH.dhKeygen (F := F) gen
  agree_eq : ∀ (a : F) (pk : ECKey),
    pqxdh.x25519_agree (privEnc a) pk = .ok (_root_.PQXDH.DH a pk)
  canonical_eq : ∀ pk : ECKey, pqxdh.ec_is_canonical pk = .ok true

def EncapsTotalAll : Prop :=
  ∀ (pk : PQPK) (coins : Coins), ∃ r, pqxdh.mlkem_encapsulate pk coins = .ok r


section GroupModelBridge

variable [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey]
  (P : Parameters SPK SSK S C Msg IdC IdK) (gen : ECKey) (privEnc : F → Bytes 32#usize)

private lemma genOPK_toSpec (hM : ECGroupModel P gen privEnc) (hasOPK : Bool) :
    genOPK P.ecKeygen hasOPK
      = Option.map (kpOfPair privEnc) <$> _root_.PQXDH.genOPK (F := F) gen hasOPK := by
  rw [hM.keygen_eq]
  cases hasOPK <;> simp [genOPK, _root_.PQXDH.genOPK, Functor.map_map]

private lemma setup_toSpec (hM : ECGroupModel P gen privEnc) (msg : Msg) :
    setup P msg
      = Prod.map (ukOfSpec privEnc) (tkOfSpec privEnc) <$>
          _root_.PQXDH.setup (specParams P F gen) msg := by
  simp only [setup, _root_.PQXDH.setup, hM.keygen_eq, map_bind, bind_map_left]
  rfl

omit [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey] in
private lemma publish_toSpec
    (rp : _root_.PQXDH.RecipientParameters F ECKey PQPK PQSK SPK SSK S) :
    publish P (rpOfSpec privEnc rp) = _root_.PQXDH.publish (specParams P F gen) rp := by
  refine bind_congr fun σ => ?_
  rcases hopk : rp.opkB with _ | opk <;>
    simp [rpOfSpec, kpOfPair, hopk, specParams]

omit [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey] in
private lemma kpOfPair_public (p : ECKey × F) :
    (kpOfPair privEnc p).public_key = p.1 :=
  rfl

private lemma pqxdh_initiate_groupModel (hM : ECGroupModel P gen privEnc)
    (p₁ p₂ : ECKey × F) (ikB spk : ECKey) (opk : Option ECKey) (pqpk : PQPK)
    (coins : Coins) {ss : SS} {ct : CT} {ks : Key × Key × Key}
    (henc : pqxdh.mlkem_encapsulate pqpk coins = .ok (ss, ct))
    (hks : deriveKeys (_root_.PQXDH.DH p₁.2 spk) (_root_.PQXDH.DH p₂.2 ikB)
      (_root_.PQXDH.DH p₂.2 spk) (Option.map (fun o => _root_.PQXDH.DH p₂.2 o) opk) ss
      = .ok ks) :
    pqxdh.pqxdh_initiate
      { our_identity_key_pair := kpOfPair privEnc p₁
        our_ephemeral_key_pair := kpOfPair privEnc p₂
        their_identity_key := ikB
        their_signed_pre_key := spk
        their_one_time_pre_key := opk
        their_kyber_pre_key := pqpk } coins
      = .ok ⟨⟨ks.1, ks.2.1, ks.2.2⟩, ct⟩ := by
  unfold pqxdh.pqxdh_initiate
  cases opk with
  | none =>
      simp only [Option.map_none] at hks
      cases hsi : pqxdh.pqxdh_secret_input (_root_.PQXDH.DH p₁.2 spk)
          (_root_.PQXDH.DH p₂.2 ikB) (_root_.PQXDH.DH p₂.2 spk) ss with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp only [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit, Aeneas.Std.bind_tc_ok,
        Aeneas.Std.Result.ok.injEq] at hks
      subst hks
      simp [kpOfPair, hM.agree_eq, Aeneas.Std.lift, henc, hsi, hokm, hsplit]
  | some o =>
      simp only [Option.map_some] at hks
      cases hsi : pqxdh.pqxdh_secret_input_with_opk (_root_.PQXDH.DH p₁.2 spk)
          (_root_.PQXDH.DH p₂.2 ikB) (_root_.PQXDH.DH p₂.2 spk)
          (_root_.PQXDH.DH p₂.2 o) ss with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp only [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit, Aeneas.Std.bind_tc_ok,
        Aeneas.Std.Result.ok.injEq] at hks
      subst hks
      simp [kpOfPair, hM.agree_eq, Aeneas.Std.lift, henc, hsi, hokm, hsplit]

private lemma pqxdh_accept_groupModel (hM : ECGroupModel P gen privEnc)
    (q₁ q₂ : ECKey × F) (opkq : Option (ECKey × F)) (pqsk : PQSK)
    (ikA ekA : ECKey) (ct : CT) {ss : SS} {ks : Key × Key × Key}
    (hdec : pqxdh.mlkem_decapsulate pqsk ct = .ok ss)
    (hks : deriveKeys (_root_.PQXDH.DH q₂.2 ikA) (_root_.PQXDH.DH q₁.2 ekA)
      (_root_.PQXDH.DH q₂.2 ekA) (Option.map (fun o => _root_.PQXDH.DH o.2 ekA) opkq) ss
      = .ok ks) :
    pqxdh.pqxdh_accept
      { our_identity_key_pair := kpOfPair privEnc q₁
        our_signed_pre_key_pair := kpOfPair privEnc q₂
        our_one_time_pre_key_pair := opkq.map (kpOfPair privEnc)
        our_kyber_secret_key := pqsk
        their_identity_key := ikA
        their_ephemeral_key := ekA
        their_kyber_ciphertext := ct } = .ok (some ⟨ks.1, ks.2.1, ks.2.2⟩) := by
  unfold pqxdh.pqxdh_accept
  cases opkq with
  | none =>
      simp only [Option.map_none] at hks ⊢
      cases hsi : pqxdh.pqxdh_secret_input (_root_.PQXDH.DH q₂.2 ikA)
          (_root_.PQXDH.DH q₁.2 ekA) (_root_.PQXDH.DH q₂.2 ekA) ss with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp only [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit, Aeneas.Std.bind_tc_ok,
        Aeneas.Std.Result.ok.injEq] at hks
      subst hks
      simp [kpOfPair, hM.canonical_eq, hM.agree_eq, Aeneas.Std.lift, hdec, hsi, hokm, hsplit]
  | some o =>
      simp only [Option.map_some] at hks ⊢
      cases hsi : pqxdh.pqxdh_secret_input_with_opk (_root_.PQXDH.DH q₂.2 ikA)
          (_root_.PQXDH.DH q₁.2 ekA) (_root_.PQXDH.DH q₂.2 ekA)
          (_root_.PQXDH.DH o.2 ekA) ss with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi] at hks
      | ok si =>
      cases hokm : pqxdh.hkdf_sha256_derive si.to_slice pqxdh.PQXDH_LABEL.to_slice with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm] at hks
      | ok okm =>
      cases hsplit : pqxdh.derive_split okm with
      | fail e => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | div => simp [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit] at hks
      | ok keys =>
      obtain ⟨rk, ck, pk⟩ := keys
      simp only [deriveKeys, Aeneas.Std.lift, hsi, hokm, hsplit, Aeneas.Std.bind_tc_ok,
        Aeneas.Std.Result.ok.injEq] at hks
      subst hks
      simp [kpOfPair, hM.canonical_eq, hM.agree_eq, Aeneas.Std.lift, hdec, hsi, hokm, hsplit]

private lemma initiate_toSpec (hM : ECGroupModel P gen privEnc)
    (hencTotal : EncapsTotalAll) (hkdfTotal : DeriveKeysTotal)
    (uk : _root_.PQXDH.InitiatorParameters F ECKey SPK Msg)
    (bundle : PreKeyBundle ECKey PQPK S IdC IdK) :
    initiate P (ukOfSpec privEnc uk) bundle
      = _root_.PQXDH.initiate (specParams P F gen) uk bundle := by
  simp only [initiate, _root_.PQXDH.initiate, ukOfSpec, specParams, hM.keygen_eq,
    bind_map_left]
  by_cases hpin : bundle.ikB = uk.ikB
  · simp only [hpin, ne_eq, not_true_eq_false, if_false]
    refine bind_congr fun _ => ?_
    refine bind_congr fun okSPK => ?_
    refine bind_congr fun okPQPK => ?_
    cases okSPK with
    | false => simp
    | true =>
    cases okPQPK with
    | false => simp
    | true =>
    simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false]
    refine bind_congr fun _ => ?_
    refine bind_congr fun a => ?_
    simp only [pqkem, bind_assoc]
    refine bind_congr fun coins => ?_
    obtain ⟨⟨ss, ct⟩, henc⟩ := hencTotal bundle.pqpkB.1 coins
    obtain ⟨ks, hks⟩ := hkdfTotal (_root_.PQXDH.DH uk.ikA.2 bundle.spkB.1)
      (_root_.PQXDH.DH a.2 uk.ikB) (_root_.PQXDH.DH a.2 bundle.spkB.1)
      (Option.map (fun o => _root_.PQXDH.DH a.2 o) (bundle.opkB.map Prod.fst)) ss
    rw [pqxdh_initiate_groupModel P gen privEnc hM uk.ikA a uk.ikB bundle.spkB.1
      (bundle.opkB.map Prod.fst) bundle.pqpkB.1 coins henc hks]
    have hmap : Option.map (fun o => _root_.PQXDH.DH a.2 o) (bundle.opkB.map Prod.fst)
        = bundle.opkB.map fun opk => _root_.PQXDH.DH a.2 opk.1 := by
      cases bundle.opkB <;> rfl
    rw [hmap] at hks
    simp [henc, hks, getOk, kpOfPair]
  · simp [hpin]

private lemma accept_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hM : ECGroupModel P gen privEnc)
    (hkdfTotal : DeriveKeysTotal)
    (rp : _root_.PQXDH.RecipientParameters F ECKey PQPK PQSK SPK SSK S)
    (im : InitialMessage ECKey CT C IdC IdK) :
    accept P (rpOfSpec privEnc rp) im = _root_.PQXDH.accept (specParams P F gen) rp im := by
  simp only [accept, _root_.PQXDH.accept, rpOfSpec, specParams, kpOfPair_public,
    Option.map_map, Function.comp_def]
  by_cases hguard : im.idSPK ≠ P.idEC rp.spkB.1 ∨ im.idPQPK ≠ P.idKEM rp.pqpkB.1 ∨
      im.idOPK ≠ Option.map (fun opk => P.idEC opk.1) rp.opkB
  · simp [hguard]
  · simp only [hguard, if_false]
    cases hdec : pqxdh.mlkem_decapsulate rp.pqpkB.2 im.ct with
    | ok ss =>
        obtain ⟨ks, hks⟩ := hkdfTotal (_root_.PQXDH.DH rp.spkB.2 im.ikA)
          (_root_.PQXDH.DH rp.ikB.2 im.ekA) (_root_.PQXDH.DH rp.spkB.2 im.ekA)
          (Option.map (fun opk => _root_.PQXDH.DH opk.2 im.ekA) rp.opkB) ss
        rw [pqxdh_accept_groupModel P gen privEnc hM rp.ikB rp.spkB rp.opkB rp.pqpkB.2
          im.ikA im.ekA im.ct hdec hks]
        simp only [pqkem, hdec, pure_bind]
        simp only [hks, getOk]
        cases P.aead.decrypt ks.2.1 (im.ikA, rp.ikB.1, rp.pqpkB.1) im.ctxt <;> rfl
    | fail e =>
        have hacc : pqxdh.pqxdh_accept
            { our_identity_key_pair := kpOfPair privEnc rp.ikB
              our_signed_pre_key_pair := kpOfPair privEnc rp.spkB
              our_one_time_pre_key_pair := rp.opkB.map (kpOfPair privEnc)
              our_kyber_secret_key := rp.pqpkB.2
              their_identity_key := im.ikA
              their_ephemeral_key := im.ekA
              their_kyber_ciphertext := im.ct } = .fail e := by
          simp [pqxdh.pqxdh_accept, kpOfPair, hM.canonical_eq, hM.agree_eq, hdec]
        rw [hacc]
        simp [pqkem, hdec]
    | div =>
        have hacc : pqxdh.pqxdh_accept
            { our_identity_key_pair := kpOfPair privEnc rp.ikB
              our_signed_pre_key_pair := kpOfPair privEnc rp.spkB
              our_one_time_pre_key_pair := rp.opkB.map (kpOfPair privEnc)
              our_kyber_secret_key := rp.pqpkB.2
              their_identity_key := im.ikA
              their_ephemeral_key := im.ekA
              their_kyber_ciphertext := im.ct } = .div := by
          simp [pqxdh.pqxdh_accept, kpOfPair, hM.canonical_eq, hM.agree_eq, hdec]
        rw [hacc]
        simp [pqkem, hdec]

omit [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey] in
private lemma confirm_toSpec [DecidableEq Msg]
    (ctx : SessionContext ECKey PQPK Msg Key) (conf : C) :
    confirm P ctx conf = _root_.PQXDH.confirm (specParams P F gen) ctx conf :=
  rfl

private lemma initiator_init_toSpec [DecidableEq Msg]
    (uk : _root_.PQXDH.InitiatorParameters F ECKey SPK Msg) :
    (initiator P).init (ukOfSpec privEnc uk)
      = Party.InitResult.map (Sum.map (ukOfSpec privEnc) id) <$>
          (_root_.PQXDH.initiator (specParams P F gen)).init uk := by
  simp only [initiator, _root_.PQXDH.initiator, map_pure, Party.InitResult.map, Sum.map_inl]

private lemma initiator_step_toSpec [DecidableEq Msg]
    (hM : ECGroupModel P gen privEnc)
    (hencTotal : EncapsTotalAll) (hkdfTotal : DeriveKeysTotal)
    (st : _root_.PQXDH.InitiatorParameters F ECKey SPK Msg ⊕
      SessionContext ECKey PQPK Msg Key ⊕ Key)
    (w : Message ECKey PQPK CT S C IdC IdK) :
    (initiator P).step (Sum.map (ukOfSpec privEnc) id st) w
      = Party.StepResult.map (Sum.map (ukOfSpec privEnc) id) <$>
          (_root_.PQXDH.initiator (specParams P F gen)).step st w := by
  rcases st with p | ctx | k
  · cases w with
    | bundle b =>
        simp only [initiator, _root_.PQXDH.initiator, Sum.map_inl,
          initiate_toSpec P gen privEnc hM hencTotal hkdfTotal p b, map_bind]
        refine bind_congr fun r => ?_
        rcases r with _ | ⟨im, ctx⟩ <;> simp [Party.StepResult.map]
    | initial im => simp [initiator, _root_.PQXDH.initiator, Party.StepResult.map]
    | confirmation c => simp [initiator, _root_.PQXDH.initiator, Party.StepResult.map]
  · cases w with
    | bundle b => simp [initiator, _root_.PQXDH.initiator, Party.StepResult.map]
    | initial im => simp [initiator, _root_.PQXDH.initiator, Party.StepResult.map]
    | confirmation conf =>
        simp only [initiator, _root_.PQXDH.initiator, Sum.map_inr, id_eq]
        rw [confirm_toSpec (F := F) P gen ctx conf]
        cases _root_.PQXDH.confirm (specParams P F gen) ctx conf <;> simp [Party.StepResult.map]
  · cases w <;> simp [initiator, _root_.PQXDH.initiator, Party.StepResult.map]

private lemma initiator_output_toSpec [DecidableEq Msg]
    (st : _root_.PQXDH.InitiatorParameters F ECKey SPK Msg ⊕
      SessionContext ECKey PQPK Msg Key ⊕ Key) :
    (initiator P).output (Sum.map (ukOfSpec privEnc) id st)
      = (_root_.PQXDH.initiator (specParams P F gen)).output st := by
  rcases st with p | ctx | k <;> rfl

private lemma recipient_init_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hM : ECGroupModel P gen privEnc) (hasOPK : Bool)
    (tk : _root_.PQXDH.RecipientIdentity F ECKey SPK SSK S) :
    (recipient P hasOPK).init (tkOfSpec privEnc tk)
      = Party.InitResult.map (Sum.map (rpOfSpec privEnc) id) <$>
          (_root_.PQXDH.recipient (specParams P F gen) hasOPK).init tk := by
  simp only [recipient, _root_.PQXDH.recipient, genOPK_toSpec P gen privEnc hM hasOPK,
    specParams, pqkem, tkOfSpec, map_bind, bind_map_left]
  refine bind_congr fun opkB => ?_
  refine bind_congr fun pqpkB => ?_
  have hrp : (⟨kpOfPair privEnc tk.ikB, tk.sigkB, kpOfPair privEnc tk.spkB,
      tk.spkSigB, Option.map (kpOfPair privEnc) opkB, pqpkB⟩ :
        RecipientParameters SPK SSK S)
      = rpOfSpec privEnc ⟨tk.ikB, tk.sigkB, tk.spkB, tk.spkSigB, opkB, pqpkB⟩ := rfl
  rw [hrp, publish_toSpec]
  refine bind_congr fun bundle => ?_
  simp [Party.InitResult.map, rpOfSpec]

private lemma recipient_step_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hM : ECGroupModel P gen privEnc)
    (hkdfTotal : DeriveKeysTotal) (hasOPK : Bool)
    (st : _root_.PQXDH.RecipientParameters F ECKey PQPK PQSK SPK SSK S ⊕ Key)
    (w : Message ECKey PQPK CT S C IdC IdK) :
    (recipient P hasOPK).step (Sum.map (rpOfSpec privEnc) id st) w
      = Party.StepResult.map (Sum.map (rpOfSpec privEnc) id) <$>
          (_root_.PQXDH.recipient (specParams P F gen) hasOPK).step st w := by
  rcases st with rp | k
  · cases w with
    | bundle b => simp [recipient, _root_.PQXDH.recipient, Party.StepResult.map]
    | initial im =>
        simp only [recipient, _root_.PQXDH.recipient, Sum.map_inl,
          accept_toSpec P gen privEnc hM hkdfTotal rp im, map_bind]
        refine bind_congr fun r => ?_
        rcases r with _ | ctx <;> simp [Party.StepResult.map, specParams]
    | confirmation c => simp [recipient, _root_.PQXDH.recipient, Party.StepResult.map]
  · cases w <;> simp [recipient, _root_.PQXDH.recipient, Party.StepResult.map]

private lemma recipient_output_toSpec [DecidableEq IdC] [DecidableEq IdK] (hasOPK : Bool)
    (st : _root_.PQXDH.RecipientParameters F ECKey PQPK PQSK SPK SSK S ⊕ Key) :
    (recipient P hasOPK).output (Sum.map (rpOfSpec privEnc) id st)
      = (_root_.PQXDH.recipient (specParams P F gen) hasOPK).output st := by
  rcases st with rp | k <;> rfl

variable {msg : Msg} {hasOPK : Bool}

def _root_.AKE.UAKE.Adversary.toSpec
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters SPK SSK S C Msg IdC IdK}
    (gen : ECKey) (privEnc : F → Bytes 32#usize)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Adversary (_root_.PQXDH.uakeInitiator (specParams P F gen) msg hasOPK) where
  State := A.State
  challenge := fun uk w => A.challenge (ukOfSpec privEnc uk) w
  post := A.post

private lemma opensAtMost_toSpec
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters SPK SSK S C Msg IdC IdK}
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) {q : ℕ}
    (hq : A.OpensAtMost q) : (A.toSpec gen privEnc).OpensAtMost q :=
  ⟨fun uk w => hq.1 (ukOfSpec privEnc uk) w, hq.2⟩

private lemma initiator_sim [DecidableEq Msg]
    (hM : ECGroupModel P gen privEnc)
    (hencTotal : EncapsTotalAll) (hkdfTotal : DeriveKeysTotal) :
    Party.Sim (_root_.PQXDH.initiator (specParams P F gen)) (initiator P)
      (ukOfSpec privEnc) (Sum.map (ukOfSpec privEnc) id) where
  init_eq := initiator_init_toSpec P gen privEnc
  step_eq := initiator_step_toSpec P gen privEnc hM hencTotal hkdfTotal
  output_eq := initiator_output_toSpec P gen privEnc

private lemma recipient_sim [DecidableEq IdC] [DecidableEq IdK]
    (hM : ECGroupModel P gen privEnc) (hkdfTotal : DeriveKeysTotal) (hasOPK : Bool) :
    Party.Sim (_root_.PQXDH.recipient (specParams P F gen) hasOPK) (recipient P hasOPK)
      (tkOfSpec privEnc) (Sum.map (rpOfSpec privEnc) id) where
  init_eq := recipient_init_toSpec P gen privEnc hM hasOPK
  step_eq := recipient_step_toSpec P gen privEnc hM hkdfTotal hasOPK
  output_eq := recipient_output_toSpec P gen privEnc hasOPK

private lemma exp_toSpec
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters SPK SSK S C Msg IdC IdK}
    (hM : ECGroupModel P gen privEnc)
    (hencTotal : EncapsTotalAll) (hkdfTotal : DeriveKeysTotal)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.Exp A = UAKE.Exp (A.toSpec gen privEnc) := by
  have hsetup : (uakeInitiator P msg hasOPK).setup
      = Prod.map (ukOfSpec privEnc) (tkOfSpec privEnc) <$>
        (_root_.PQXDH.uakeInitiator (specParams P F gen) msg hasOPK).setup :=
    setup_toSpec P gen privEnc hM msg
  exact (UAKE.Exp_transport
    (proto₁ := _root_.PQXDH.uakeInitiator (specParams P F gen) msg hasOPK)
    (proto₂ := uakeInitiator P msg hasOPK)
    (initiator_sim P gen privEnc hM hencTotal hkdfTotal)
    (recipient_sim P gen privEnc hM hkdfTotal hasOPK) rfl hsetup A).trans rfl

private lemma advantage_toSpec
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    {P : Parameters SPK SSK S C Msg IdC IdK}
    (hM : ECGroupModel P gen privEnc)
    (hencTotal : EncapsTotalAll) (hkdfTotal : DeriveKeysTotal)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.advantage A = UAKE.advantage (A.toSpec gen privEnc) := by
  unfold UAKE.advantage
  rw [exp_toSpec gen privEnc hM hencTotal hkdfTotal A]

omit [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey] in
private lemma kdfPRF_specParams {P : Parameters SPK SSK S C Msg IdC IdK} :
    _root_.PQXDH.kdfPRF (specParams P F gen) = kdfPRF :=
  rfl

private lemma kdfPRFDH_advantage_toSpec {P : Parameters SPK SSK S C Msg IdC IdK}
    (hM : ECGroupModel P gen privEnc)
    (D : PRFScheme.PRFAdversary (ECKey × ECKey × Option ECKey × SS) (Key × Key × Key)) :
    (_root_.PQXDH.kdfPRFDH (specParams P F gen)).prfAdvantage D
      = (kdfPRFDH P).prfAdvantage D := by
  have hreal : (_root_.PQXDH.kdfPRFDH (specParams P F gen)).prfRealExp D
      = (kdfPRFDH P).prfRealExp D := by
    unfold PRFScheme.prfRealExp
    rw [show (kdfPRFDH P).keygen = P.ecKeygen from rfl, hM.keygen_eq,
      show _root_.PQXDH.dhKeygen (F := F) gen
        = (do let a ← $ᵗ F; pure (a • gen, a)) from rfl]
    simp only [bind_map_left, bind_assoc, pure_bind]
    exact bind_congr fun c => rfl
  unfold PRFScheme.prfAdvantage
  rw [hreal]

private lemma nominalDDHExpReal_toSpec (hM : ECGroupModel P gen privEnc)
    (D : DiffieHellman.NominalDDHAdversary ECKey) :
    DiffieHellman.nominalDDHExpReal P.ecKeygen pqxdh.KeyPair.public_key x25519DH D
      = DiffieHellman.nominalDDHExpReal (DiffieHellman.groupKeygen (F := F) gen)
          Prod.fst (fun kp pk => kp.2 • pk) D := by
  unfold DiffieHellman.nominalDDHExpReal
  rw [hM.keygen_eq, show _root_.PQXDH.dhKeygen (F := F) gen
    = DiffieHellman.groupKeygen (F := F) gen from rfl]
  simp only [bind_map_left]
  refine bind_congr fun kpA => ?_
  refine bind_congr fun kpB => ?_
  simp [x25519DH, kpOfPair, hM.agree_eq, getOk, _root_.PQXDH.DH]

private lemma nominalDDHExpRand_toSpec (hM : ECGroupModel P gen privEnc)
    (D : DiffieHellman.NominalDDHAdversary ECKey) :
    DiffieHellman.nominalDDHExpRand P.ecKeygen pqxdh.KeyPair.public_key D
      = DiffieHellman.nominalDDHExpRand (DiffieHellman.groupKeygen (F := F) gen)
          Prod.fst D := by
  unfold DiffieHellman.nominalDDHExpRand
  rw [hM.keygen_eq, show _root_.PQXDH.dhKeygen (F := F) gen
    = DiffieHellman.groupKeygen (F := F) gen from rfl]
  simp only [bind_map_left]
  exact bind_congr fun kpA => bind_congr fun kpB => bind_congr fun kpC => rfl

private lemma ddh_advantage_toSpec {P : Parameters SPK SSK S C Msg IdC IdK}
    (hM : ECGroupModel P gen privEnc)
    (D : _root_.DiffieHellman.DDHAdversary F ECKey) :
    _root_.DiffieHellman.ddhDistAdvantage gen D
      = DiffieHellman.nominalDDHDistAdvantage P.ecKeygen pqxdh.KeyPair.public_key
          x25519DH (D gen) := by
  rw [DiffieHellman.ddhDistAdvantage_eq_nominalDDHDistAdvantage]
  unfold DiffieHellman.nominalDDHDistAdvantage
  rw [nominalDDHExpReal_toSpec P gen privEnc hM (D gen),
    nominalDDHExpRand_toSpec P gen privEnc hM (D gen)]

end GroupModelBridge

theorem uakeInitiator_secure_pq_ofGroupModel
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    {F : Type} [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey]
    (P : Parameters SPK SSK S C Msg IdC IdK) (gen : ECKey) (privEnc : F → Bytes 32#usize)
    (msg : Msg) (hasOPK : Bool)
    (hM : ECGroupModel P gen privEnc)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εkem εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : ECKey ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hkemCorrect : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hkem : ∀ B : (pqkem P).IND_CCA_Adversary,
      KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hencTotal : EncapsTotalAll)
    (hkdfTotal : DeriveKeysTotal)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (ECKey × ECKey × ECKey × Option ECKey)
        (Key × Key × Key),
      kdfPRF.prfAdvantage D ≤ εkdf) :
    UAKE.advantage A ≤ 3 * εsig + q * (εkem + 3 * εaead + εkdf) := by
  rw [advantage_toSpec gen privEnc hM hencTotal hkdfTotal A]
  exact _root_.PQXDH.uakeInitiator_secure_pq (specParams P F gen) msg hasOPK hidKEM
    (A.toSpec gen privEnc) q (opensAtMost_toSpec gen privEnc A hq)
    εsig εkem εaead εkdf hverifyDet hkemCorrect hsig hkem haead
    (fun D => by rw [kdfPRF_specParams]; exact hkdf D)

theorem uakeInitiator_secure_dh_ofGroupModel
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    {F : Type} [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey]
    (P : Parameters SPK SSK S C Msg IdC IdK) (gen : ECKey) (privEnc : F → Bytes 32#usize)
    (msg : Msg) (hasOPK : Bool)
    (hM : ECGroupModel P gen privEnc)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εddh εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : ECKey ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hddh : ∀ D : DiffieHellman.NominalDDHAdversary ECKey,
      DiffieHellman.nominalDDHDistAdvantage P.ecKeygen pqxdh.KeyPair.public_key
        x25519DH D ≤ εddh)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hencTotal : EncapsTotalAll)
    (hkdfTotal : DeriveKeysTotal)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (ECKey × ECKey × Option ECKey × SS)
        (Key × Key × Key),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf) :
    UAKE.advantage A ≤ εsig + q * (εddh + εaead + εkdf) := by
  rw [advantage_toSpec gen privEnc hM hencTotal hkdfTotal A]
  exact _root_.PQXDH.uakeInitiator_secure_dh (specParams P F gen) msg hasOPK hidKEM
    (A.toSpec gen privEnc) q (opensAtMost_toSpec gen privEnc A hq)
    εsig εddh εaead εkdf hverifyDet hsig
    (fun D => by
      have h := hddh (D gen)
      rw [← ddh_advantage_toSpec gen privEnc hM D] at h
      exact h)
    haead
    (fun D => by rw [kdfPRFDH_advantage_toSpec gen privEnc hM D]; exact hkdf D)

theorem uakeInitiator_secure_pq
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εkem εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : ECKey ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hkemCorrect : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hkem : ∀ B : (pqkem P).IND_CCA_Adversary,
      KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hencTotal : EncapsTotal P)
    (hkdfTotal : DeriveKeysTotal)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (ECKey × ECKey × ECKey × Option ECKey)
        (Key × Key × Key),
      kdfPRF.prfAdvantage D ≤ εkdf) :
    UAKE.advantage A ≤ 3 * εsig + q * (εkem + 3 * εaead + εkdf) := by
  have hGroupModel : ∃ (F : Type) (_ : Field F) (_ : SampleableType F)
      (_ : AddCommGroup ECKey) (_ : Module F ECKey)
      (gen : ECKey) (privEnc : F → Bytes 32#usize),
      ECGroupModel P gen privEnc := by
    sorry
  have hencTotalAll : EncapsTotalAll := by
    sorry
  obtain ⟨F, iField, iSamp, iGroup, iMod, gen, privEnc, hM⟩ := hGroupModel
  letI := iField; letI := iSamp; letI := iGroup; letI := iMod
  exact uakeInitiator_secure_pq_ofGroupModel P gen privEnc msg hasOPK hM hidKEM A q hq
    εsig εkem εaead εkdf hverifyDet hkemCorrect hsig hkem haead hencTotalAll hkdfTotal
    hkdf

theorem uakeInitiator_secure_dh
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εddh εaead εkdf : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : ECKey ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hdh : AgreeComm P)
    (hagree : AgreeTotal P)
    (hddh : ∀ D : DiffieHellman.NominalDDHAdversary ECKey,
      DiffieHellman.nominalDDHDistAdvantage P.ecKeygen pqxdh.KeyPair.public_key
        x25519DH D ≤ εddh)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead)
    (hkdfTotal : DeriveKeysTotal)
    (hkdf : ∀ D : PRFScheme.PRFAdversary (ECKey × ECKey × Option ECKey × SS)
        (Key × Key × Key),
      (kdfPRFDH P).prfAdvantage D ≤ εkdf) :
    UAKE.advantage A ≤ εsig + q * (εddh + εaead + εkdf) := by
  have hGroupModel : ∃ (F : Type) (_ : Field F) (_ : SampleableType F)
      (_ : AddCommGroup ECKey) (_ : Module F ECKey)
      (gen : ECKey) (privEnc : F → Bytes 32#usize),
      ECGroupModel P gen privEnc := by
    sorry
  have hencTotalAll : EncapsTotalAll := by
    sorry
  obtain ⟨F, iField, iSamp, iGroup, iMod, gen, privEnc, hM⟩ := hGroupModel
  letI := iField; letI := iSamp; letI := iGroup; letI := iMod
  exact uakeInitiator_secure_dh_ofGroupModel P gen privEnc msg hasOPK hM hidKEM A q hq
    εsig εddh εaead εkdf hverifyDet hsig hddh haead hencTotalAll hkdfTotal hkdf

end Security

end

end PQXDH.Aeneas
