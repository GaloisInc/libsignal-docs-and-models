/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas2.Extracted.Protocol
import PQXDH.Spec.Basic
import PQXDH.Spec.UAKE
import ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import ToVCVio.CryptoFoundations.AKE.UAKE.Transport
import PQXDH.HardnessAssumptions.DiffieHellman

/-!
# PQXDH as a UAKE, instantiated with the Aeneas extraction of `libsignal_protocol`
-/

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas2

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

abbrev ECPub : Type := libsignal_core.curve.PublicKey

abbrev ECPriv : Type := libsignal_core.curve.PrivateKey

abbrev ECKeyPair : Type := libsignal_core.curve.KeyPair

abbrev IdKey : Type := identity_key.IdentityKey

abbrev IdKeyPair : Type := identity_key.IdentityKeyPair

abbrev PQPub : Type := kem.Key kem.Public

abbrev PQPriv : Type := kem.Key kem.Secret

abbrev PQKeyPair : Type := kem.KeyPair

abbrev CT : Type := Aeneas.Std.Slice Aeneas.Std.U8

abbrev Key : Type := Bytes 32#usize

abbrev HandshakeKeys : Type := pqxdh.HandshakeKeys

abbrev InitiatorAgreement : Type := pqxdh.InitiatorAgreement

local instance : DecidableEq ECPub := Classical.decEq _

local instance : DecidableEq PQPub := Classical.decEq _

local instance : DecidableEq (Aeneas.Std.Slice Aeneas.Std.U8) := Classical.decEq _

local instance : Inhabited (Aeneas.Std.Slice Aeneas.Std.U8) :=
  ⟨Aeneas.Std.Slice.new _⟩

local instance : Inhabited Key := ⟨Aeneas.Std.Array.repeat 32#usize 0#u8⟩

local instance : Inhabited kem.KeyType := ⟨kem.KeyType.Kyber1024⟩

local instance {T : Type} : Inhabited (kem.KeyMaterial T) :=
  ⟨{ data := default, kind := () }⟩

local instance {T : Type} : Inhabited (kem.Key T) :=
  ⟨{ key_type := default, key_data := default }⟩

def toKey (s : Aeneas.Std.Slice Aeneas.Std.U8) : Option Key :=
  if h : s.val.length = (32#usize : Aeneas.Std.Usize).val then some ⟨s.val, h⟩ else none

def identityKeyOf (kp : ECKeyPair) : IdKey := { public_key := kp.public_key }

def identityKeyPairOf (kp : ECKeyPair) : IdKeyPair :=
  { identity_key := identityKeyOf kp, private_key := kp.private_key }

variable {Rand SPK SSK S C Msg IdC IdK : Type}

structure Parameters (Rand SPK SSK S C Msg IdC IdK : Type) where
  rngInst : rand.rng.Rng Rand
  cryptoRngInst : rand_core_1.CryptoRng Rand
  coins : ProbComp Rand
  ecKeygen : ProbComp ECKeyPair
  pqKeygen : ProbComp PQKeyPair
  sig : SignatureAlg ProbComp (ECPub ⊕ PQPub) SPK SSK S
  aead : AEAD.Scheme ProbComp Msg Key (ECPub × ECPub × PQPub) C
  idEC : ECPub → IdC
  idKEM : PQPub → IdK

def runRaw {α : Type} (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (f : Rand → Aeneas.Std.Result (α × Rand)) : ProbComp (Option α) := do
  let r ← P.coins
  match f r with
  | .ok (x, _) => return some x
  | _ => return none

def runRes {α : Type} (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (f : Rand →
      Aeneas.Std.Result
        (Aeneas.Std.core.result.Result α error.SignalProtocolError × Rand)) :
    ProbComp (Option α) := do
  let r ← P.coins
  match f r with
  | .ok (.Ok x, _) => return some x
  | _ => return none

def getRes {α : Type}
    (r : Aeneas.Std.Result (Aeneas.Std.core.result.Result α error.SignalProtocolError)) :
    Option α :=
  match r with
  | .ok (.Ok x) => some x
  | _ => none

def genEC (P : Parameters Rand SPK SSK S C Msg IdC IdK) : ProbComp (Option ECKeyPair) :=
  runRaw P (libsignal_core.curve.KeyPair.generate P.rngInst P.cryptoRngInst)

def genKem (P : Parameters Rand SPK SSK S C Msg IdC IdK) : ProbComp (Option PQKeyPair) :=
  runRaw P (kem.KeyPair.generate P.rngInst P.cryptoRngInst kem.KeyType.Kyber1024)

def genOPK (P : Parameters Rand SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    ProbComp (Option ECKeyPair) :=
  if hasOPK then some <$> P.ecKeygen else pure none

def runInitiate (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (ip : pqxdh.InitiatorParameters) : ProbComp (Option InitiatorAgreement) :=
  runRes P (pqxdh.pqxdh_initiate P.rngInst P.cryptoRngInst ip)

def runAccept (rp : pqxdh.RecipientParameters) : Option HandshakeKeys :=
  getRes (pqxdh.pqxdh_accept rp)

def rootKeyBytes (hk : HandshakeKeys) : Key := hk.root_key.key

def chainKeyBytes (hk : HandshakeKeys) : Key := hk.chain_key.key

def pqrKeyBytes (hk : HandshakeKeys) : Key := hk.pqr_key

def pqkem (P : Parameters Rand SPK SSK S C Msg IdC IdK) :
    KEMScheme ProbComp Key PQPub PQPriv CT where
  keygen := do
    let kp ← P.pqKeygen
    return (kp.public_key, kp.secret_key)
  encaps := fun pk => do
    let r ← P.coins
    match kem.KeyPublic.encapsulate P.cryptoRngInst pk r with
    | .ok (.Ok (ss, ct), _) =>
      match toKey ss with
      | some k => return (ct, k)
      | none => return default
    | _ => return default
  decaps := fun sk ct =>
    return (getRes (kem.KeySecret.decapsulate sk ct)).bind toKey

def InitiateTotal (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ ip : pqxdh.InitiatorParameters, ∀ r ∈ support P.coins,
    ∃ agr rest, pqxdh.pqxdh_initiate P.rngInst P.cryptoRngInst ip r = .ok (.Ok agr, rest)

def AcceptTotal : Prop :=
  ∀ rp : pqxdh.RecipientParameters, ∃ hk, pqxdh.pqxdh_accept rp = .ok (.Ok hk)

def AgreeComm (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ kp₁ ∈ support P.ecKeygen, ∀ kp₂ ∈ support P.ecKeygen,
    libsignal_core.curve.PrivateKey.calculate_agreement kp₁.private_key kp₂.public_key
      = libsignal_core.curve.PrivateKey.calculate_agreement kp₂.private_key kp₁.public_key

def AgreeTotal (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ kp₁ ∈ support P.ecKeygen, ∀ kp₂ ∈ support P.ecKeygen,
    ∃ z, libsignal_core.curve.PrivateKey.calculate_agreement kp₁.private_key kp₂.public_key
      = .ok (.Ok z)

structure InitiatorParameters (SPK Msg : Type) where
  ikA : IdKeyPair
  ikB : IdKey
  sigpkB : SPK
  msg : Msg

structure RecipientIdentity (SPK SSK S : Type) where
  ikB : IdKeyPair
  sigkB : SPK × SSK
  spkB : ECKeyPair
  spkSigB : S

structure RecipientParameters (SPK SSK S : Type) where
  ikB : IdKeyPair
  sigkB : SPK × SSK
  spkB : ECKeyPair
  spkSigB : S
  opkB : Option ECKeyPair
  pqpkB : PQKeyPair

def setup (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) :
    ProbComp (InitiatorParameters SPK Msg × RecipientIdentity SPK SSK S) := do
  let ikA ← P.ecKeygen
  let ikB ← P.ecKeygen
  let sigkB ← P.sig.keygen
  let spkB ← P.ecKeygen
  let spkSigB ← P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)
  return ({ ikA := identityKeyPairOf ikA, ikB := identityKeyOf ikB,
            sigpkB := sigkB.1, msg := msg },
    { ikB := identityKeyPairOf ikB, sigkB := sigkB, spkB := spkB, spkSigB := spkSigB })

def publish (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (p : RecipientParameters SPK SSK S) :
    ProbComp (PreKeyBundle ECPub PQPub S IdC IdK) := do
  let pqpkSigB ← P.sig.sign p.sigkB.1 p.sigkB.2 (EncodeKEM p.pqpkB.public_key)
  return { ikB := p.ikB.identity_key.public_key
           spkB := (p.spkB.public_key, P.idEC p.spkB.public_key)
           spkSigB := p.spkSigB
           pqpkB := (p.pqpkB.public_key, P.idKEM p.pqpkB.public_key)
           pqpkSigB := pqpkSigB
           opkB := p.opkB.map fun opk => (opk.public_key, P.idEC opk.public_key) }

def initiate (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (p : InitiatorParameters SPK Msg)
    (bundle : PreKeyBundle ECPub PQPub S IdC IdK) :
    ProbComp (Option (InitialMessage ECPub CT C IdC IdK ×
      SessionContext ECPub PQPub Msg Key)) := do
  if bundle.ikB ≠ p.ikB.public_key then return none
  let okSPK ← P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB
  let okPQPK ← P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB
  if !(okSPK && okPQPK) then return none
  let ekA ← P.ecKeygen
  match ← runInitiate P
      { our_identity_key_pair := p.ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := { public_key := bundle.ikB }
        their_signed_pre_key := bundle.spkB.1
        their_one_time_pre_key := bundle.opkB.map Prod.fst
        their_ratchet_key := bundle.spkB.1
        their_kyber_pre_key := bundle.pqpkB.1
        self_session := false } with
  | some agreement =>
      let SK := rootKeyBytes agreement.keys
      let KA := chainKeyBytes agreement.keys
      let KB := pqrKeyBytes agreement.keys
      let AD := (p.ikA.identity_key.public_key, bundle.ikB, bundle.pqpkB.1)
      let ctxt ← P.aead.encrypt KA AD p.msg
      return some ({ ikA := p.ikA.identity_key.public_key
                     ekA := ekA.public_key
                     ct := agreement.kyber_ciphertext
                     idSPK := bundle.spkB.2
                     idPQPK := bundle.pqpkB.2
                     idOPK := bundle.opkB.map Prod.snd
                     ctxt := ctxt },
        { sk := SK, kb := KB, ad := AD, msg := p.msg })
  | none => return none

def accept [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (p : RecipientParameters SPK SSK S)
    (msg : InitialMessage ECPub CT C IdC IdK) :
    ProbComp (Option (SessionContext ECPub PQPub Msg Key)) := do
  if msg.idSPK ≠ P.idEC p.spkB.public_key ∨ msg.idPQPK ≠ P.idKEM p.pqpkB.public_key ∨
      msg.idOPK ≠ p.opkB.map (fun opk => P.idEC opk.public_key) then return none
  match runAccept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_pre_key_pair := p.pqpkB
        their_identity_key := { public_key := msg.ikA }
        their_ephemeral_key := msg.ekA
        their_kyber_ciphertext := msg.ct
        self_session := false } with
  | some keys =>
      let AD := (msg.ikA, p.ikB.identity_key.public_key, p.pqpkB.public_key)
      match P.aead.decrypt (chainKeyBytes keys) AD msg.ctxt with
      | some m =>
          return some { sk := rootKeyBytes keys, kb := pqrKeyBytes keys, ad := AD, msg := m }
      | none => return none
  | none => return none

def confirm [DecidableEq Msg] (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (ctx : SessionContext ECPub PQPub Msg Key) (conf : C) : Option Key :=
  if P.aead.decrypt ctx.kb ctx.ad conf = some ctx.msg then some ctx.sk
  else none

def initiator [DecidableEq Msg] (P : Parameters Rand SPK SSK S C Msg IdC IdK) :
    Party ProbComp (InitiatorParameters SPK Msg)
      (Message ECPub PQPub CT S C IdC IdK) (Option Key) where
  State := InitiatorParameters SPK Msg ⊕ SessionContext ECPub PQPub Msg Key ⊕ Key
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
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity SPK SSK S)
      (Message ECPub PQPub CT S C IdC IdK) (Option Key) where
  State := RecipientParameters SPK SSK S ⊕ Key
  init := fun idn => do
    let opkB ← genOPK P hasOPK
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
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp Key (InitiatorParameters SPK Msg)
      (RecipientIdentity SPK SSK S)
      (Message ECPub PQPub CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiator P
  T := recipient P hasOPK

def uakeRecipient [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp Key (RecipientIdentity SPK SSK S)
      (InitiatorParameters SPK Msg)
      (Message ECPub PQPub CT S C IdC IdK) where
  rounds := 4
  setup := Prod.swap <$> setup P msg
  U := recipient P hasOPK
  T := initiator P

section CorrectnessLemmas

attribute [local simp]
  core.result.Result.Insts.CoreOpsTry_traitTry.branch
  Aeneas.Std.core.result.Result.Insts.CoreOpsTry.branch
  core.result.Result.Insts.CoreOpsTry_traitFromResidualResultInfallibleE.from_residual
  Aeneas.Std.core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
  identity_key.IdentityKeyPair.impl.private_key
  identity_key.IdentityKey.impl.public_key
  identityKeyPairOf identityKeyOf

/- Believed true, not provable as the extraction stands. Aeneas erases `Box<T>` to `T`
(note this axiom's type is `T → Result T`), so `Box::as_ref` can only be the identity; it is
an `axiom` rather than a definition because the extraction's external-model file supplies no
body. Unlike `encaps_toKey_isSome` this is a modelling stub, not a knowledge gap: giving that
axiom its evident model `fun x => .ok x` would discharge it outright. -/
private lemma as_ref_eq_ok (ss : Aeneas.Std.Slice Aeneas.Std.U8) :
    Box.Insts.CoreConvertAsRef.as_ref Aeneas.Std.Global ss = .ok ss := sorry

/- Believed true, not provable here. ML-KEM shared secrets are 32 bytes (FIPS 203), so `toKey`
never fails on them, but the KEM bottoms out in the opaque axiom
`kem.kyber1024.…encapsulate` whose type constrains no lengths — libcrux's ML-KEM is not
extracted. Discharging this needs a length-refined model of that axiom, or extraction of the
implementation. -/
private lemma encaps_toKey_isSome {R : Type}
    (inst : rand_core_1.CryptoRng R) (pk : PQPub) (r : R)
    {ss ct : Aeneas.Std.Slice Aeneas.Std.U8} {rest : R}
    (h : kem.KeyPublic.encapsulate inst pk r = .ok (.Ok (ss, ct), rest)) :
    (toKey ss).isSome := sorry

private lemma toKey_inj {s₁ s₂ : Aeneas.Std.Slice Aeneas.Std.U8} {k : Key}
    (h₁ : toKey s₁ = some k) (h₂ : toKey s₂ = some k) : s₁ = s₂ := by
  unfold toKey at h₁ h₂
  split at h₁
  · split at h₂
    · simp only [Option.some.injEq] at h₁ h₂
      subst h₁
      exact Subtype.ext (by simpa using congrArg Subtype.val h₂.symm)
    · exact absurd h₂ (by simp)
  · exact absurd h₁ (by simp)

private lemma getRes_eq_some {α : Type}
    {r : Aeneas.Std.Result (Aeneas.Std.core.result.Result α error.SignalProtocolError)}
    {x : α} (h : getRes r = some x) : r = .ok (.Ok x) := by
  unfold getRes at h
  split at h <;> simp_all

private lemma probOutput_probComp_evalDist {α : Type} (oa : ProbComp α) (x : α) :
    Pr[= x | ProbCompRuntime.probComp.evalDist oa] = Pr[= x | oa] := by
  rfl

private lemma support_eq_singleton_true_of_evalDist {oa : ProbComp Bool}
    (h : Pr[= true | ProbCompRuntime.probComp.evalDist oa] = 1) :
    support oa = {true} := by
  rw [probOutput_probComp_evalDist, probOutput_eq_one_iff] at h
  exact h.2

private lemma verify_eq_true_of_perfectlyComplete
    (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    {kp : SPK × SSK} (hkp : kp ∈ support P.sig.keygen)
    (m : ECPub ⊕ PQPub) {σ : S} (hσ : σ ∈ support (P.sig.sign kp.1 kp.2 m))
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

private lemma aead_decrypt_encrypt_of_perfectlyCorrect [DecidableEq Msg]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (k : Key) (ad : ECPub × ECPub × PQPub) (m : Msg) {c : C}
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

private lemma opkB_mem_of_genOPK {P : Parameters Rand SPK SSK S C Msg IdC IdK}
    {hasOPK : Bool} {opkB : Option ECKeyPair}
    (h : opkB ∈ support (genOPK P hasOPK)) :
    ∀ x ∈ opkB, x ∈ support P.ecKeygen := by
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

private lemma kem_decapsulate_eq_ok
    (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    {kp : PQKeyPair} (hkp : kp ∈ support P.pqKeygen)
    {coins : Rand} (hcoins : coins ∈ support P.coins)
    {ss ct : Aeneas.Std.Slice Aeneas.Std.U8} {rest : Rand}
    (henc : kem.KeyPublic.encapsulate P.cryptoRngInst kp.public_key coins
      = .ok (.Ok (ss, ct), rest)) :
    kem.KeySecret.decapsulate kp.secret_key ct = .ok (.Ok ss) := by
  have h := support_eq_singleton_true_of_evalDist hkem
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp
    (encaps_toKey_isSome P.cryptoRngInst kp.public_key coins henc)
  have hkeygen : (kp.public_key, kp.secret_key) ∈ support (pqkem P).keygen := by
    simp only [pqkem, mem_support_bind_iff, support_pure, Set.mem_singleton_iff]
    exact ⟨kp, hkp, rfl⟩
  have hct : (ct, k) ∈ support ((pqkem P).encaps kp.public_key) := by
    simp only [pqkem, mem_support_bind_iff]
    exact ⟨coins, hcoins, by simp [henc, hk]⟩
  have key : ∀ r ∈ support ((pqkem P).decaps kp.secret_key ct), r = some k := by
    intro r hr
    have hmem : decide (r = some k) ∈ support ((pqkem P).CorrectExp) := by
      unfold KEMScheme.CorrectExp
      refine (mem_support_bind_iff _ _ _).mpr ⟨(kp.public_key, kp.secret_key), hkeygen, ?_⟩
      refine (mem_support_bind_iff _ _ _).mpr ⟨(ct, k), hct, ?_⟩
      refine (mem_support_bind_iff _ _ _).mpr ⟨r, hr, ?_⟩
      simp
    rw [h] at hmem
    simpa using hmem
  have hd := key ((getRes (kem.KeySecret.decapsulate kp.secret_key ct)).bind toKey)
    (by simp [pqkem])
  obtain ⟨ss', hss', hkss'⟩ := Option.bind_eq_some_iff.mp hd
  rw [getRes_eq_some hss', toKey_inj hkss' hk]

private lemma from_residual_err_ne {E F T U : Type}
    (inst : Aeneas.Std.core.convert.From F E) (e : E) (c r : U) (x : T)
    (h : (do
           let v ← Aeneas.Std.core.convert.From.from inst e
           Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Err v, c))
         = Aeneas.Std.Result.ok (Aeneas.Std.core.result.Result.Ok x, r)) : False := by
  cases hf : Aeneas.Std.core.convert.From.from inst e <;> simp_all

set_option maxHeartbeats 2000000 in
private lemma pqxdh_accept_eq_of_initiate_eq_ok
    (rngInst : rand.rng.Rng Rand) (cryptoRngInst : rand_core_1.CryptoRng Rand)
    (ikA ekA ikB spkB : ECKeyPair) (opkB : Option ECKeyPair)
    (pqkp : PQKeyPair) (coins rest : Rand) (ag : InitiatorAgreement)
    (hdh1 : libsignal_core.curve.PrivateKey.calculate_agreement
        spkB.private_key ikA.public_key
      = libsignal_core.curve.PrivateKey.calculate_agreement
        ikA.private_key spkB.public_key)
    (hdh2 : libsignal_core.curve.PrivateKey.calculate_agreement
        ikB.private_key ekA.public_key
      = libsignal_core.curve.PrivateKey.calculate_agreement
        ekA.private_key ikB.public_key)
    (hdh3 : libsignal_core.curve.PrivateKey.calculate_agreement
        spkB.private_key ekA.public_key
      = libsignal_core.curve.PrivateKey.calculate_agreement
        ekA.private_key spkB.public_key)
    (hdh4 : ∀ opk ∈ opkB,
      libsignal_core.curve.PrivateKey.calculate_agreement
        opk.private_key ekA.public_key
      = libsignal_core.curve.PrivateKey.calculate_agreement
        ekA.private_key opk.public_key)
    (hkem : ∀ ss ct rest' ss',
      kem.KeyPublic.encapsulate cryptoRngInst pqkp.public_key coins
        = .ok (.Ok (ss, ct), rest') →
      Box.Insts.CoreConvertAsRef.as_ref Aeneas.Std.Global ss = .ok ss' →
      kem.KeySecret.decapsulate pqkp.secret_key ct = .ok (.Ok ss'))
    (hcanon : libsignal_core.curve.PublicKey.is_canonical ekA.public_key = .ok true)
    (hI : pqxdh.pqxdh_initiate rngInst cryptoRngInst
      { our_identity_key_pair := identityKeyPairOf ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := identityKeyOf ikB
        their_signed_pre_key := spkB.public_key
        their_one_time_pre_key := opkB.map (·.public_key)
        their_ratchet_key := spkB.public_key
        their_kyber_pre_key := pqkp.public_key
        self_session := false } coins = .ok (.Ok ag, rest)) :
    pqxdh.pqxdh_accept
      { our_identity_key_pair := identityKeyPairOf ikB
        our_signed_pre_key_pair := spkB
        our_one_time_pre_key_pair := opkB
        our_kyber_pre_key_pair := pqkp
        their_identity_key := identityKeyOf ikA
        their_ephemeral_key := ekA.public_key
        their_kyber_ciphertext := ag.kyber_ciphertext
        self_session := false } = .ok (.Ok ag.keys) := by
  simp only [pqxdh.pqxdh_initiate] at hI
  simp only [pqxdh.pqxdh_accept, hcanon]
  simp only [identity_key.IdentityKeyPair.impl.private_key,
    identity_key.IdentityKey.impl.public_key, identityKeyPairOf, identityKeyOf] at hI ⊢
  cases hmul : 32#usize * 6#usize with
  | fail e => simp [hmul] at hI
  | div => simp [hmul] at hI
  | ok i =>
  cases hsl : Aeneas.Std.lift (Aeneas.Std.Array.repeat 32#usize 255#u8).to_slice with
  | fail e => simp [hmul, hsl] at hI
  | div => simp [hmul, hsl] at hI
  | ok s =>
  cases hex1 : Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8
      (Aeneas.Std.alloc.vec.Vec.with_capacity Aeneas.Std.U8 i) s with
  | fail e => simp [hmul, hsl, hex1] at hI
  | div => simp [hmul, hsl, hex1] at hI
  | ok secrets1 =>
  cases hd1 : libsignal_core.curve.PrivateKey.calculate_agreement
      ikA.private_key spkB.public_key with
  | fail e => simp [hmul, hsl, hex1, hd1] at hI
  | div => simp [hmul, hsl, hex1, hd1] at hI
  | ok cr1 =>
  cases cr1 with
  | Err e =>
      simp [hmul, hsl, hex1, hd1] at hI <;>
        cases hf : Aeneas.Std.core.convert.From.from
          error.SignalProtocolError.Insts.CoreConvertFromCurveError e <;> simp_all
  | Ok dh1 =>
  cases hex2 : Aeneas.Std.alloc.vec.Vec.extend_from_slice
      Aeneas.Std.core.clone.CloneU8 secrets1 dh1 with
  | fail e => simp [hmul, hsl, hex1, hd1, hex2] at hI
  | div => simp [hmul, hsl, hex1, hd1, hex2] at hI
  | ok secrets2 =>
  cases hd2 : libsignal_core.curve.PrivateKey.calculate_agreement
      ekA.private_key ikB.public_key with
  | fail e => simp [hmul, hsl, hex1, hd1, hex2, hd2] at hI
  | div => simp [hmul, hsl, hex1, hd1, hex2, hd2] at hI
  | ok cr2 =>
  cases cr2 with
  | Err e =>
      simp [hmul, hsl, hex1, hd1, hex2, hd2] at hI <;>
        cases hf : Aeneas.Std.core.convert.From.from
          error.SignalProtocolError.Insts.CoreConvertFromCurveError e <;> simp_all
  | Ok dh2 =>
  cases hex3 : Aeneas.Std.alloc.vec.Vec.extend_from_slice
      Aeneas.Std.core.clone.CloneU8 secrets2 dh2 with
  | fail e => simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3] at hI
  | div => simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3] at hI
  | ok secrets3 =>
  cases hd3 : libsignal_core.curve.PrivateKey.calculate_agreement
      ekA.private_key spkB.public_key with
  | fail e => simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3] at hI
  | div => simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3] at hI
  | ok cr3 =>
  cases cr3 with
  | Err e =>
      simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3] at hI <;>
        cases hf : Aeneas.Std.core.convert.From.from
          error.SignalProtocolError.Insts.CoreConvertFromCurveError e <;> simp_all
  | Ok dh3 =>
  cases hex4 : Aeneas.Std.alloc.vec.Vec.extend_from_slice
      Aeneas.Std.core.clone.CloneU8 secrets3 dh3 with
  | fail e => simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4] at hI
  | div => simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4] at hI
  | ok secrets4 =>
  cases opkB with
  | none =>
    cases henc : kem.KeyPublic.encapsulate cryptoRngInst pqkp.public_key coins with
    | fail e => simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, henc] at hI
    | div => simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, henc] at hI
    | ok p =>
      obtain ⟨cr4, csprng1⟩ := p
      cases cr4 with
      | Err e =>
          simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, henc] at hI
      | Ok sct =>
        obtain ⟨ss, ct⟩ := sct
        cases hasr : Box.Insts.CoreConvertAsRef.as_ref Aeneas.Std.Global ss with
        | fail e =>
            simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, henc, hasr] at hI
        | div =>
            simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, henc, hasr] at hI
        | ok s1 =>
          cases hex5 : Aeneas.Std.alloc.vec.Vec.extend_from_slice
              Aeneas.Std.core.clone.CloneU8 secrets4 s1 with
          | fail e =>
              simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, henc, hasr, hex5] at hI
          | div =>
              simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, henc, hasr, hex5] at hI
          | ok secrets5 =>
            cases hder : pqxdh.HandshakeKeys.derive secrets5.deref with
            | fail e =>
                simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, henc, hasr, hex5,
                  hder] at hI
            | div =>
                simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, henc, hasr, hex5,
                  hder] at hI
            | ok hk =>
              simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, henc, hasr, hex5,
                hder] at hI
              obtain ⟨hag, -⟩ := hI
              subst hag
              simp [hmul, hsl, hex1, hex2, hex3, hex4, hex5, hder, hdh1, hdh2, hdh3,
                hd1, hd2, hd3, hkem ss ct csprng1 s1 henc hasr]
  | some opk =>
    cases hd4 : libsignal_core.curve.PrivateKey.calculate_agreement
        ekA.private_key opk.public_key with
    | fail e => simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4] at hI
    | div => simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4] at hI
    | ok cr4 =>
      cases cr4 with
      | Err e =>
          simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4] at hI <;>
            cases hf : Aeneas.Std.core.convert.From.from
              error.SignalProtocolError.Insts.CoreConvertFromCurveError e <;> simp_all
      | Ok dh4 =>
        cases hex5 : Aeneas.Std.alloc.vec.Vec.extend_from_slice
            Aeneas.Std.core.clone.CloneU8 secrets4 dh4 with
        | fail e =>
            simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4, hex5] at hI
        | div =>
            simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4, hex5] at hI
        | ok secrets5 =>
          cases henc : kem.KeyPublic.encapsulate cryptoRngInst pqkp.public_key coins with
          | fail e =>
              simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4, hex5, henc] at hI
          | div =>
              simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4, hex5, henc] at hI
          | ok p =>
            obtain ⟨cr5, csprng1⟩ := p
            cases cr5 with
            | Err e =>
                simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4, hex5, henc] at hI
            | Ok sct =>
              obtain ⟨ss, ct⟩ := sct
              cases hasr : Box.Insts.CoreConvertAsRef.as_ref Aeneas.Std.Global ss with
              | fail e =>
                  simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4, hex5, henc,
                    hasr] at hI
              | div =>
                  simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4, hex5, henc,
                    hasr] at hI
              | ok s1 =>
                cases hex6 : Aeneas.Std.alloc.vec.Vec.extend_from_slice
                    Aeneas.Std.core.clone.CloneU8 secrets5 s1 with
                | fail e =>
                    simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4, hex5, henc,
                      hasr, hex6] at hI
                | div =>
                    simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4, hex5, henc,
                      hasr, hex6] at hI
                | ok secrets6 =>
                  cases hder : pqxdh.HandshakeKeys.derive secrets6.deref with
                  | fail e =>
                      simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4, hex5,
                        henc, hasr, hex6, hder] at hI
                  | div =>
                      simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4, hex5,
                        henc, hasr, hex6, hder] at hI
                  | ok hk =>
                    simp [hmul, hsl, hex1, hd1, hex2, hd2, hex3, hd3, hex4, hd4, hex5,
                      henc, hasr, hex6, hder] at hI
                    obtain ⟨hag, -⟩ := hI
                    subst hag
                    simp [hmul, hsl, hex1, hex2, hex3, hex4, hex5, hex6, hder, hdh1, hdh2,
                      hdh3, hdh4 opk rfl, hd1, hd2, hd3, hd4,
                      hkem ss ct csprng1 s1 henc hasr]

private lemma mem_support_initiate
    (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    {p : InitiatorParameters SPK Msg} {bundle : PreKeyBundle ECPub PQPub S IdC IdK}
    {r : Option (InitialMessage ECPub CT C IdC IdK × SessionContext ECPub PQPub Msg Key)}
    (hpin : bundle.ikB = p.ikB.public_key)
    (hok₁ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeEC bundle.spkB.1) bundle.spkSigB),
      b = true)
    (hok₂ : ∀ b ∈ support (P.sig.verify p.sigpkB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB),
      b = true)
    (hr : r ∈ support (initiate P p bundle)) :
    r = none ∨
      ∃ ekA ∈ support P.ecKeygen, ∃ coins ∈ support P.coins,
      ∃ ag : InitiatorAgreement, ∃ rest : Rand,
        pqxdh.pqxdh_initiate P.rngInst P.cryptoRngInst
          { our_identity_key_pair := p.ikA
            our_ephemeral_key_pair := ekA
            their_identity_key := { public_key := p.ikB.public_key }
            their_signed_pre_key := bundle.spkB.1
            their_one_time_pre_key := bundle.opkB.map Prod.fst
            their_ratchet_key := bundle.spkB.1
            their_kyber_pre_key := bundle.pqpkB.1
            self_session := false } coins = .ok (.Ok ag, rest) ∧
      ∃ ctxt ∈ support (P.aead.encrypt (chainKeyBytes ag.keys)
          (p.ikA.identity_key.public_key, p.ikB.public_key, bundle.pqpkB.1) p.msg),
        r = some (⟨p.ikA.identity_key.public_key, ekA.public_key, ag.kyber_ciphertext,
            bundle.spkB.2, bundle.pqpkB.2, bundle.opkB.map Prod.snd, ctxt⟩,
          ⟨rootKeyBytes ag.keys, pqrKeyBytes ag.keys,
            (p.ikA.identity_key.public_key, p.ikB.public_key, bundle.pqpkB.1), p.msg⟩) := by
  simp only [initiate, hpin, ne_eq, not_true_eq_false, if_false,
    mem_support_bind_iff] at hr
  obtain ⟨_, _, okSPK, hok, okPQPK, hok', hr⟩ := hr
  obtain rfl := hok₁ _ hok
  obtain rfl := hok₂ _ hok'
  simp only [Bool.and_self, Bool.not_true, Bool.false_eq_true, if_false,
    mem_support_bind_iff] at hr
  obtain ⟨_, _, ekA, hekA, agOpt, hag, hr⟩ := hr
  simp only [runInitiate, runRes, mem_support_bind_iff] at hag
  obtain ⟨coins, hcoins, hag⟩ := hag
  cases hI : pqxdh.pqxdh_initiate P.rngInst P.cryptoRngInst
      { our_identity_key_pair := p.ikA
        our_ephemeral_key_pair := ekA
        their_identity_key := { public_key := p.ikB.public_key }
        their_signed_pre_key := bundle.spkB.1
        their_one_time_pre_key := bundle.opkB.map Prod.fst
        their_ratchet_key := bundle.spkB.1
        their_kyber_pre_key := bundle.pqpkB.1
        self_session := false } coins with
  | ok pr =>
      obtain ⟨cr, rest⟩ := pr
      cases cr with
      | Ok ag =>
          rw [hI] at hag
          simp only [support_pure, Set.mem_singleton_iff] at hag
          subst hag
          simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hr
          obtain ⟨ctxt, hctxt, rfl⟩ := hr
          exact Or.inr ⟨ekA, hekA, coins, hcoins, ag, rest, hI, ctxt, hctxt, rfl⟩
      | Err e =>
          rw [hI] at hag
          simp only [support_pure, Set.mem_singleton_iff] at hag
          subst hag
          simp only [support_pure, Set.mem_singleton_iff] at hr
          exact Or.inl hr
  | fail e =>
      rw [hI] at hag
      simp only [support_pure, Set.mem_singleton_iff] at hag
      subst hag
      simp only [support_pure, Set.mem_singleton_iff] at hr
      exact Or.inl hr
  | div =>
      rw [hI] at hag
      simp only [support_pure, Set.mem_singleton_iff] at hag
      subst hag
      simp only [support_pure, Set.mem_singleton_iff] at hr
      exact Or.inl hr

private lemma accept_eq_pure_some
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    {p : RecipientParameters SPK SSK S} {im : InitialMessage ECPub CT C IdC IdK}
    {keys : HandshakeKeys} {m₀ : Msg}
    (hid₁ : im.idSPK = P.idEC p.spkB.public_key)
    (hid₂ : im.idPQPK = P.idKEM p.pqpkB.public_key)
    (hid₃ : im.idOPK = p.opkB.map (fun opk => P.idEC opk.public_key))
    (hacc : pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_pre_key_pair := p.pqpkB
        their_identity_key := { public_key := im.ikA }
        their_ephemeral_key := im.ekA
        their_kyber_ciphertext := im.ct
        self_session := false } = .ok (.Ok keys))
    (hdec : P.aead.decrypt (chainKeyBytes keys)
        (im.ikA, p.ikB.identity_key.public_key, p.pqpkB.public_key) im.ctxt = some m₀) :
    accept P p im = pure (some ⟨rootKeyBytes keys, pqrKeyBytes keys,
      (im.ikA, p.ikB.identity_key.public_key, p.pqpkB.public_key), m₀⟩) := by
  simp [accept, runAccept, getRes, hid₁, hid₂, hid₃, hacc, hdec]

private lemma accept_eq_pure_none
    [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    {p : RecipientParameters SPK SSK S} {im : InitialMessage ECPub CT C IdC IdK}
    (hacc : ∀ keys, pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_pre_key_pair := p.pqpkB
        their_identity_key := { public_key := im.ikA }
        their_ephemeral_key := im.ekA
        their_kyber_ciphertext := im.ct
        self_session := false } ≠ .ok (.Ok keys)) :
    accept P p im = pure none := by
  cases hr : pqxdh.pqxdh_accept
      { our_identity_key_pair := p.ikB
        our_signed_pre_key_pair := p.spkB
        our_one_time_pre_key_pair := p.opkB
        our_kyber_pre_key_pair := p.pqpkB
        their_identity_key := { public_key := im.ikA }
        their_ephemeral_key := im.ekA
        their_kyber_ciphertext := im.ct
        self_session := false } with
  | ok o =>
      cases o with
      | Err e => simp [accept, runAccept, getRes, hr]
      | Ok keys => exact absurd hr (hacc keys)
  | fail e => simp [accept, runAccept, getRes, hr]
  | div => simp [accept, runAccept, getRes, hr]

private lemma pqxdh_accept_ne_ok_some
    {rp : pqxdh.RecipientParameters} {res : Aeneas.Std.Result Bool}
    (hc : libsignal_core.curve.PublicKey.is_canonical rp.their_ephemeral_key = res)
    (hres : res ≠ .ok true) :
    ∀ keys, pqxdh.pqxdh_accept rp ≠ .ok (.Ok keys) := by
  intro keys h
  unfold pqxdh.pqxdh_accept at h
  rw [hc] at h
  cases res with
  | ok b =>
      cases b with
      | true => exact hres rfl
      | false =>
          cases hs : Str.Insts.AllocBorrowToOwnedString.to_owned
            (Aeneas.Std.toStr "incoming base key is invalid"
              pqxdh.pqxdh_accept._proof_1) <;> simp_all
  | fail e => simp at h
  | div => simp at h

private lemma run_support_initiator
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P)
    (msg : Msg)
    {ikA ikB spkB : ECKeyPair} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support P.ecKeygen)
    (hikB : ikB ∈ support P.ecKeygen)
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support P.ecKeygen)
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)))
    {uOut tOut : Option (Option Key)}
    (hrun : (uOut, tOut) ∈ support (Party.runHonest (initiator P) (recipient P hasOPK)
      ⟨identityKeyPairOf ikA, identityKeyOf ikB, sigkB.1, msg⟩
      ⟨identityKeyPairOf ikB, sigkB, spkB, spkSigB⟩ (3 + 1))) :
    uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join := by
  simp only [Party.runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, rfl, qInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩,
    hrun⟩ := hrun
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
    rfl | ⟨ekA, hekA, coins, hcoins, ag, rest, hI, ctxt, hctxt, rfl⟩
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
        = Option.map (fun opk : ECKeyPair => opk.public_key) opkB := by
      cases opkB <;> rfl
    rw [hmap] at hI
    have hidOPK : Option.map Prod.snd
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map (fun opk => P.idEC opk.public_key) opkB := by
      cases opkB <;> rfl
    cases hc : libsignal_core.curve.PublicKey.is_canonical ekA.public_key with
    | ok b =>
      cases b with
      | true =>
        have hacc := pqxdh_accept_eq_of_initiate_eq_ok P.rngInst P.cryptoRngInst
          ikA ekA ikB spkB opkB pqpkB coins rest ag
          (hdh spkB hspkB ikA hikA) (hdh ikB hikB ekA hekA) (hdh spkB hspkB ekA hekA)
          (fun opk hopk => hdh opk (hopkB opk hopk) ekA hekA)
          (fun ss ct rest' ss' henc hasr => by
            have hid := as_ref_eq_ok ss
            rw [hid] at hasr
            simp only [Aeneas.Std.Result.ok.injEq] at hasr
            subst hasr
            exact kem_decapsulate_eq_ok P hkem hpqpkB hcoins henc)
          hc hI
        have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
        rw [accept_eq_pure_some P rfl rfl hidOPK hacc hdecA] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsr
        obtain ⟨conf, hconf, rfl⟩ := hsr
        have hconfirm := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hconf
        simp only [identityKeyPairOf, identityKeyOf] at hconfirm
        simp only [confirm, identityKeyPairOf, identityKeyOf, hconfirm, reduceIte,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
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
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P)
    (msg : Msg)
    {ikA ikB spkB : ECKeyPair} {sigkB : SPK × SSK} {spkSigB : S}
    (hikA : ikA ∈ support P.ecKeygen)
    (hikB : ikB ∈ support P.ecKeygen)
    (hsigkB : sigkB ∈ support P.sig.keygen)
    (hspkB : spkB ∈ support P.ecKeygen)
    (hspkSigB : spkSigB ∈ support (P.sig.sign sigkB.1 sigkB.2 (EncodeEC spkB.public_key)))
    {uOut tOut : Option (Option Key)}
    (hrun : (uOut, tOut) ∈ support (Party.runHonest (recipient P hasOPK) (initiator P)
      ⟨identityKeyPairOf ikB, sigkB, spkB, spkSigB⟩
      ⟨identityKeyPairOf ikA, identityKeyOf ikB, sigkB.1, msg⟩ (4 + 1))) :
    uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join := by
  simp only [Party.runHonest, initiator, recipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at hrun
  obtain ⟨pInit, ⟨opkB, hopkB_mem, pqpkB, hpqpkB, bundle, hbundle, rfl⟩, qInit, rfl,
    hrun⟩ := hrun
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
    rfl | ⟨ekA, hekA, coins, hcoins, ag, rest, hI, ctxt, hctxt, rfl⟩
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
        = Option.map (fun opk : ECKeyPair => opk.public_key) opkB := by
      cases opkB <;> rfl
    rw [hmap] at hI
    have hidOPK : Option.map Prod.snd
        (Option.map (fun opk => (opk.public_key, P.idEC opk.public_key)) opkB)
        = Option.map (fun opk => P.idEC opk.public_key) opkB := by
      cases opkB <;> rfl
    cases hc : libsignal_core.curve.PublicKey.is_canonical ekA.public_key with
    | ok b =>
      cases b with
      | true =>
        have hacc := pqxdh_accept_eq_of_initiate_eq_ok P.rngInst P.cryptoRngInst
          ikA ekA ikB spkB opkB pqpkB coins rest ag
          (hdh spkB hspkB ikA hikA) (hdh ikB hikB ekA hekA) (hdh spkB hspkB ekA hekA)
          (fun opk hopk => hdh opk (hopkB opk hopk) ekA hekA)
          (fun ss ct rest' ss' henc hasr => by
            have hid := as_ref_eq_ok ss
            rw [hid] at hasr
            simp only [Aeneas.Std.Result.ok.injEq] at hasr
            subst hasr
            exact kem_decapsulate_eq_ok P hkem hpqpkB hcoins henc)
          hc hI
        have hdecA := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hctxt
        rw [accept_eq_pure_some P rfl rfl hidOPK hacc hdecA] at har
        simp only [support_pure, Set.mem_singleton_iff] at har
        subst har
        simp only [mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hsr
        obtain ⟨conf, hconf, rfl⟩ := hsr
        have hconfirm := aead_decrypt_encrypt_of_perfectlyCorrect P haead _ _ _ hconf
        simp only [identityKeyPairOf, identityKeyOf] at hconfirm
        simp only [confirm, identityKeyPairOf, identityKeyOf, hconfirm, reduceIte,
          mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at hy
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
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
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
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
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

def specParams (P : Parameters Rand SPK SSK S C Msg IdC IdK) (F : Type) (gen : ECPub) :
    PQXDH.Parameters F ECPub Key PQPub PQPriv CT SPK SSK S C Msg Key IdC IdK := sorry

structure ECGroupModel {F : Type} [Field F] [SampleableType F]
    [AddCommGroup ECPub] [Module F ECPub]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (gen : ECPub)
    (privEnc : F → ECPriv) : Prop where

theorem uakeInitiator_secure_pq
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidKEM : Function.Injective P.idKEM)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εkem εaead εkdf : ℝ)
    (hkemCorrect : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (hkem : ∀ B : (pqkem P).IND_CCA_Adversary,
      KEMScheme.IND_CCA_Advantage ProbCompRuntime.probComp B ≤ εkem)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead) :
    UAKE.advantage A ≤ εsig + εkem + εaead + εkdf := sorry

theorem uakeInitiator_secure_dh
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hidEC : Function.Injective P.idEC)
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εsig εdh εaead εkdf : ℝ)
    (hkemCorrect : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig)
    (haead : ∀ B : AEAD.INT_CTXT_D_Adversary P.aead,
      AEAD.INT_CTXT_D_Advantage P.aead B ≤ εaead) :
    UAKE.advantage A ≤ εsig + εdh + εaead + εkdf := sorry

end Security

end

end PQXDH.Aeneas2
