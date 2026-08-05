/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Simplified.Extracted.Pqxdh
import PQXDH.Spec.Basic
import PQXDH.Spec.UAKE
import ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import PQXDH.AKE.UAKE.Transport
import PQXDH.AKE.UAKE.RunHonest
import ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

/-!
# PQXDH as a UAKE, instantiated with the Aeneas-extracted implementation
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace PQXDH.Aeneas.Simplified

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

end

end PQXDH.Aeneas.Simplified
