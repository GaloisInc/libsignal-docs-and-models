/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.Extracted.Protocol
import PQXDH.Spec.Basic
import PQXDH.Spec.UAKE
import ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import ToVCVio.CryptoFoundations.AKE.UAKE.Transport
import ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# PQXDH as a UAKE, instantiated with the Aeneas extraction of `libsignal_protocol`
-/

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

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

scoped instance : DecidableEq ECPub := Classical.decEq _

scoped instance : DecidableEq PQPub := Classical.decEq _

scoped instance : DecidableEq (Aeneas.Std.Slice Aeneas.Std.U8) := Classical.decEq _

scoped instance : Inhabited (Aeneas.Std.Slice Aeneas.Std.U8) :=
  ⟨Aeneas.Std.Slice.new _⟩

scoped instance : Inhabited Key := ⟨Aeneas.Std.Array.repeat 32#usize 0#u8⟩

scoped instance : Inhabited kem.KeyType := ⟨kem.KeyType.Kyber1024⟩

scoped instance {T : Type} : Inhabited (kem.KeyMaterial T) :=
  ⟨{ data := default, kind := () }⟩

scoped instance {T : Type} : Inhabited (kem.Key T) :=
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

def sigMsgParts (m : Aeneas.Std.Slice Aeneas.Std.U8) :
    Aeneas.Std.Result (Aeneas.Std.Slice (Aeneas.Std.Slice Aeneas.Std.U8)) :=
  Aeneas.Std.lift (Aeneas.Std.Array.to_slice (Aeneas.Std.Array.make 1#usize [m]))

def extractedSig (rngInst : rand.rng.Rng Rand) (cryptoRngInst : rand_core_1.CryptoRng Rand)
    (coins : ProbComp Rand) (keygen : ProbComp ECKeyPair)
    (encMsg : ECPub ⊕ PQPub → Aeneas.Std.Slice Aeneas.Std.U8) :
    SignatureAlg ProbComp (ECPub ⊕ PQPub) ECPub ECPriv
      (Aeneas.Std.Slice Aeneas.Std.U8) where
  keygen := do
    let kp ← keygen
    return (kp.public_key, kp.private_key)
  sign := fun _pk sk m => do
    let r ← coins
    match libsignal_core.curve.PrivateKey.calculate_signature cryptoRngInst rngInst sk
        (encMsg m) r with
    | .ok (.Ok σ, _) => return σ
    | _ => return default
  verify := fun pk m σ =>
    match sigMsgParts (encMsg m) with
    | .ok parts =>
        match libsignal_core.curve.PublicKey.verify_signature_for_multipart_message pk
            parts σ with
        | .ok b => return b
        | _ => return false
    | _ => return false

def ECKeyPairValid (kp : ECKeyPair) : Prop :=
  libsignal_core.curve.PrivateKey.public_key kp.private_key = .ok (.Ok kp.public_key)

structure SigModel
    (P : Parameters Rand ECPub ECPriv (Aeneas.Std.Slice Aeneas.Std.U8) C Msg IdC IdK)
    (encMsg : ECPub ⊕ PQPub → Aeneas.Std.Slice Aeneas.Std.U8) : Prop where
  sig_eq : P.sig = extractedSig P.rngInst P.cryptoRngInst P.coins P.ecKeygen encMsg
  keygen_valid : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp

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

end

end PQXDH.Aeneas.Full
