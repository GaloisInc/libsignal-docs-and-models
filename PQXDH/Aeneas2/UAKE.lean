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

local instance : DecidableEq ECPub := Classical.decEq _

local instance : DecidableEq PQPub := Classical.decEq _

local instance : DecidableEq CT := Classical.decEq _

def getOk {α : Type} [Inhabited α] :
    Aeneas.Std.Result (Aeneas.Std.core.result.Result α error.SignalProtocolError) → α
  | .ok (.Ok x) => x
  | _ => default

def rootKeyBytes (hk : HandshakeKeys) : Key := sorry

def chainKeyBytes (hk : HandshakeKeys) : Key := sorry

def InitiateTotal : Prop := sorry

def AcceptTotal : Prop := sorry

variable {SPK SSK S C Msg IdC IdK : Type}

structure Parameters (SPK SSK S C Msg IdC IdK : Type) where
  ecKeygen : ProbComp ECKeyPair
  pqKeygen : ProbComp PQKeyPair
  sig : SignatureAlg ProbComp (ECPub ⊕ PQPub) SPK SSK S
  aead : AEAD.Scheme ProbComp Msg Key (ECPub × ECPub × PQPub) C
  idEC : ECPub → IdC
  idKEM : PQPub → IdK

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

def pqkem (P : Parameters SPK SSK S C Msg IdC IdK) :
    KEMScheme ProbComp Key PQPub PQPriv CT := sorry

def AgreeComm (P : Parameters SPK SSK S C Msg IdC IdK) : Prop := sorry

def AgreeTotal (P : Parameters SPK SSK S C Msg IdC IdK) : Prop := sorry

def kdfPRF : PRFScheme Key (ECPub × ECPub × ECPub × Option ECPub) (Key × Key × Key) := sorry

def setup (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) :
    ProbComp (InitiatorParameters SPK Msg × RecipientIdentity SPK SSK S) := sorry

def publish (P : Parameters SPK SSK S C Msg IdC IdK)
    (R : RecipientParameters SPK SSK S) : ProbComp Unit := sorry

def initiate (P : Parameters SPK SSK S C Msg IdC IdK)
    (I : InitiatorParameters SPK Msg) : ProbComp Unit := sorry

def accept [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK)
    (R : RecipientParameters SPK SSK S) : ProbComp Unit := sorry

def confirm [DecidableEq Msg] (P : Parameters SPK SSK S C Msg IdC IdK) :
    ProbComp Unit := sorry

def initiator [DecidableEq Msg] (P : Parameters SPK SSK S C Msg IdC IdK) :
    Party ProbComp (InitiatorParameters SPK Msg)
      (Message ECPub PQPub CT S C IdC IdK) (Option Key) := sorry

def recipient [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    Party ProbComp (RecipientIdentity SPK SSK S)
      (Message ECPub PQPub CT S C IdC IdK) (Option Key) := sorry

def uakeInitiator [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp Key (InitiatorParameters SPK Msg)
      (RecipientIdentity SPK SSK S)
      (Message ECPub PQPub CT S C IdC IdK) where
  rounds := 3
  setup := setup P msg
  U := initiator P
  T := recipient P hasOPK

def uakeRecipient [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool) :
    UAKE.Scheme ProbComp Key (RecipientIdentity SPK SSK S)
      (InitiatorParameters SPK Msg)
      (Message ECPub PQPub CT S C IdC IdK) where
  rounds := 4
  setup := Prod.swap <$> setup P msg
  U := recipient P hasOPK
  T := initiator P

theorem uakeInitiator_perfectlyCorrect
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) := sorry

theorem uakeRecipient_perfectlyCorrect
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) := sorry

section Security

def specParams (P : Parameters SPK SSK S C Msg IdC IdK) (F : Type) (gen : ECPub) :
    PQXDH.Parameters F ECPub Key PQPub PQPriv CT SPK SSK S C Msg Key IdC IdK := sorry

structure ECGroupModel {F : Type} [Field F] [SampleableType F]
    [AddCommGroup ECPub] [Module F ECPub]
    (P : Parameters SPK SSK S C Msg IdC IdK) (gen : ECPub)
    (privEnc : F → ECPriv) : Prop where

theorem uakeInitiator_secure_pq
    [DecidableEq S] [DecidableEq C] [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    [Inhabited S] [Inhabited SSK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
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
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
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
