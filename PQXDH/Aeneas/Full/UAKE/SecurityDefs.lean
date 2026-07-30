/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.UAKE.CommonLemmas

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

noncomputable section

variable {Rand SPK SSK S C Msg IdC IdK : Type}

def getOk {α : Type} [Inhabited α] : Aeneas.Std.Result α → α
  | .ok x => x
  | _ => default

def pubBytes (p : ECPub) : Key :=
  match p.key with
  | .DjbPublicKey a => a

def pubOfBytes (b : Key) : ECPub := { key := .DjbPublicKey b }

scoped instance : Inhabited ECPub := ⟨pubOfBytes default⟩

def sliceOfKey (k : Key) : Aeneas.Std.Result (Aeneas.Std.Slice Aeneas.Std.U8) :=
  Aeneas.Std.lift (Aeneas.Std.Array.to_slice k)

def pubSlice (p : ECPub) : Aeneas.Std.Result (Aeneas.Std.Slice Aeneas.Std.U8) :=
  sliceOfKey (pubBytes p)

def pubOfSlice (s : Aeneas.Std.Slice Aeneas.Std.U8) : ECPub :=
  pubOfBytes ((toKey s).getD default)

def kdfInput (dh1 dh2 dh3 : Aeneas.Std.Slice Aeneas.Std.U8)
    (dh4 : Option (Aeneas.Std.Slice Aeneas.Std.U8))
    (ss : Aeneas.Std.Slice Aeneas.Std.U8) :
    Aeneas.Std.Result (Aeneas.Std.Slice Aeneas.Std.U8) := do
  let i ← 32#usize * 6#usize
  let secrets := Aeneas.Std.alloc.vec.Vec.with_capacity Aeneas.Std.U8 i
  let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice
    (Aeneas.Std.Array.repeat 32#usize 255#u8))
  let secrets1 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets s
  let secrets2 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets1 dh1
  let secrets3 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets2 dh2
  let secrets4 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets3 dh3
  let secrets5 ← match dh4 with
    | none => pure secrets4
    | some d => Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets4 d
  let secrets6 ← Aeneas.Std.alloc.vec.Vec.extend_from_slice Aeneas.Std.core.clone.CloneU8 secrets5 ss
  pure (Aeneas.Std.alloc.vec.Vec.deref secrets6)

def deriveHK (dh1 dh2 dh3 : ECPub) (dh4 : Option ECPub) (ss : Key) :
    Aeneas.Std.Result pqxdh.HandshakeKeys := do
  let s1 ← pubSlice dh1
  let s2 ← pubSlice dh2
  let s3 ← pubSlice dh3
  let s4 ← match dh4 with
    | none => pure none
    | some d => do let x ← pubSlice d; pure (some x)
  let ssS ← sliceOfKey ss
  let inp ← kdfInput s1 s2 s3 s4 ssS
  pqxdh.HandshakeKeys.derive inp

def deriveKeys (dh1 dh2 dh3 : ECPub) (dh4 : Option ECPub) (ss : Key) :
    Aeneas.Std.Result (Key × Key × Key) := do
  let hk ← deriveHK dh1 dh2 dh3 dh4 ss
  pure (rootKeyBytes hk, chainKeyBytes hk, pqrKeyBytes hk)

def DeriveKeysTotal : Prop :=
  ∀ (dh1 dh2 dh3 : ECPub) (dh4 : Option ECPub) (ss : Key),
    ∃ hk, deriveHK dh1 dh2 dh3 dh4 ss = .ok hk

def EncapsTotalAll (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ (pk : PQPub) (r : Rand),
    ∃ ss ct rest, kem.KeyPublic.encapsulate P.cryptoRngInst pk r = .ok (.Ok (ss, ct), rest)

def ecAgree (kp : ECKeyPair) (pk : ECPub) : ECPub :=
  match libsignal_core.curve.PrivateKey.calculate_agreement kp.private_key pk with
  | .ok (.Ok z) => pubOfSlice z
  | _ => default

def specParams (P : Parameters Rand SPK SSK S C Msg IdC IdK) (F : Type) (gen : ECPub) :
    PQXDH.Parameters F ECPub Key PQPub PQPriv CT SPK SSK S C Msg Key IdC IdK where
  gen := gen
  pqkem := pqkem P
  sig := P.sig
  aead := P.aead
  kdf := fun km => getOk (deriveKeys km.1 km.2.1 km.2.2.1 km.2.2.2.1 km.2.2.2.2)
  idEC := P.idEC
  idKEM := P.idKEM

def kdfPRF : PRFScheme Key (ECPub × ECPub × ECPub × Option ECPub) (Key × Key × Key) where
  keygen := $ᵗ Key
  eval := fun ss q => getOk (deriveKeys q.1 q.2.1 q.2.2.1 q.2.2.2 ss)

variable {F : Type}

def kpOfPair (privEnc : F → ECPriv) (p : ECPub × F) : ECKeyPair where
  public_key := p.1
  private_key := privEnc p.2

def kdfPRFDH (P : Parameters Rand SPK SSK S C Msg IdC IdK) :
    PRFScheme ECKeyPair (ECPub × ECPub × Option ECPub × Key) (Key × Key × Key) where
  keygen := P.ecKeygen
  eval := fun kp q => getOk (deriveKeys q.1 q.2.1 kp.public_key q.2.2.1 q.2.2.2)

def kpOfKem (pq : PQPub × PQPriv) : PQKeyPair where
  public_key := pq.1
  secret_key := pq.2

def ukOfSpec (privEnc : F → ECPriv)
    (uk : PQXDH.InitiatorParameters F ECPub SPK Msg) :
    InitiatorParameters SPK Msg where
  ikA := identityKeyPairOf (kpOfPair privEnc uk.ikA)
  ikB := { public_key := uk.ikB }
  sigpkB := uk.sigpkB
  msg := uk.msg

def tkOfSpec (privEnc : F → ECPriv)
    (tk : PQXDH.RecipientIdentity F ECPub SPK SSK S) :
    RecipientIdentity SPK SSK S where
  ikB := identityKeyPairOf (kpOfPair privEnc tk.ikB)
  sigkB := tk.sigkB
  spkB := kpOfPair privEnc tk.spkB
  spkSigB := tk.spkSigB

def rpOfSpec (privEnc : F → ECPriv)
    (rp : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S) :
    RecipientParameters SPK SSK S where
  ikB := identityKeyPairOf (kpOfPair privEnc rp.ikB)
  sigkB := rp.sigkB
  spkB := kpOfPair privEnc rp.spkB
  spkSigB := rp.spkSigB
  opkB := rp.opkB.map (kpOfPair privEnc)
  pqpkB := kpOfKem rp.pqpkB

def ECKeygenSpec [Field F] [SampleableType F]
    [AddCommGroup ECPub] [Module F ECPub]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (gen : ECPub)
    (privEnc : F → ECPriv) : Prop :=
  P.ecKeygen = kpOfPair privEnc <$> PQXDH.dhKeygen (F := F) gen

def ECAgreeSpec [Field F] [AddCommGroup ECPub] [Module F ECPub]
    (privEnc : F → ECPriv) : Prop :=
  ∀ (a : F) (pk : ECPub),
    libsignal_core.curve.PrivateKey.calculate_agreement (privEnc a) pk
      = .ok (.Ok (getOk (pubSlice (PQXDH.DH a pk))))

def ECCanonicalSpec : Prop :=
  ∀ pk : ECPub, libsignal_core.curve.PublicKey.is_canonical pk = .ok true

def PQKeygenSpec (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop :=
  P.pqKeygen = kpOfKem <$> (pqkem P).keygen

structure ECGroupModel {F : Type} [Field F] [SampleableType F]
    [AddCommGroup ECPub] [Module F ECPub]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (gen : ECPub)
    (privEnc : F → ECPriv) : Prop where
  keygen_eq : ECKeygenSpec P gen privEnc
  agree_eq : ECAgreeSpec privEnc
  canonical_eq : ECCanonicalSpec

structure KemPairModel (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop where
  keygen_eq : PQKeygenSpec P

end

end PQXDH.Aeneas.Full
