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

abbrev SS : Type := Aeneas.Std.Slice Aeneas.Std.U8

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

variable {Rand SPK SSK S C Msg IdC IdK : Type}

structure Parameters (Rand SPK SSK S C Msg IdC IdK : Type) where
  rngInst : rand.rng.Rng Rand
  cryptoRngInst : rand_core_1.CryptoRng Rand
  coins : ProbComp Rand
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

def initiate (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (ip : pqxdh.InitiatorParameters) : ProbComp (Option InitiatorAgreement) :=
  runRes P (pqxdh.pqxdh_initiate P.rngInst P.cryptoRngInst ip)

def accept (rp : pqxdh.RecipientParameters) : Option HandshakeKeys :=
  getRes (pqxdh.pqxdh_accept rp)

def rootKeyBytes (hk : HandshakeKeys) : Key := hk.root_key.key

def chainKeyBytes (hk : HandshakeKeys) : Key := hk.chain_key.key

def pqrKeyBytes (hk : HandshakeKeys) : Key := hk.pqr_key

def sessionKey (hk : HandshakeKeys) : Key := rootKeyBytes hk

def pqkem (P : Parameters Rand SPK SSK S C Msg IdC IdK) :
    KEMScheme ProbComp Key PQPub PQPriv CT where
  keygen := do
    match ← genKem P with
    | some kp => return (kp.public_key, kp.secret_key)
    | none => return default
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

def toExtractedInitiator (I : InitiatorParameters SPK Msg) (ekA : ECKeyPair)
    (spkB rkB : ECPub) (opkB : Option ECPub) (pqpkB : PQPub) :
    pqxdh.InitiatorParameters where
  our_identity_key_pair := I.ikA
  our_ephemeral_key_pair := ekA
  their_identity_key := I.ikB
  their_signed_pre_key := spkB
  their_one_time_pre_key := opkB
  their_ratchet_key := rkB
  their_kyber_pre_key := pqpkB
  self_session := false

def toExtractedRecipient (R : RecipientParameters SPK SSK S) (ikA : IdKey)
    (ekA : ECPub) (ct : CT) : pqxdh.RecipientParameters where
  our_identity_key_pair := R.ikB
  our_signed_pre_key_pair := R.spkB
  our_one_time_pre_key_pair := R.opkB
  our_kyber_pre_key_pair := R.pqpkB
  their_identity_key := ikA
  their_ephemeral_key := ekA
  their_kyber_ciphertext := ct
  self_session := false

def AgreeComm (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop := sorry

def AgreeTotal (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop := sorry

def kdfPRF : PRFScheme Key (ECPub × ECPub × ECPub × Option ECPub) (Key × Key × Key) := sorry

def setup (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) :
    ProbComp (InitiatorParameters SPK Msg × RecipientIdentity SPK SSK S) := sorry

def publish (P : Parameters Rand SPK SSK S C Msg IdC IdK)
    (R : RecipientParameters SPK SSK S) : ProbComp Unit := sorry

def confirm [DecidableEq Msg] (P : Parameters Rand SPK SSK S C Msg IdC IdK) :
    ProbComp Unit := sorry

def initiator [DecidableEq Msg] (P : Parameters Rand SPK SSK S C Msg IdC IdK) :
    Party ProbComp (InitiatorParameters SPK Msg)
      (Message ECPub PQPub CT S C IdC IdK) (Option Key) := sorry

def recipient [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity SPK SSK S)
      (Message ECPub PQPub CT S C IdC IdK) (Option Key) := sorry

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

theorem uakeInitiator_perfectlyCorrect
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hinit : InitiateTotal P)
    (hacc : AcceptTotal) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) := sorry

theorem uakeRecipient_perfectlyCorrect
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hinit : InitiateTotal P)
    (hacc : AcceptTotal) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) := sorry

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
