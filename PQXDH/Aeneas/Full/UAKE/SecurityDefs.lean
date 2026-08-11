/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.UAKE.Assumptions

/-!
# Security Definitions for the High-fidelity Aeneas Extraction

Definitions that appear in the hypotheses of the top-level security theorems
in `Security.lean`, together with the Lean-level mirror of the extracted KDF
and the packaging of the extracted primitives as Spec-model parameters.

Model idealizations
* **Clean-group model (`ECGroupModel`):** the security theorems assume the
  opaque curve25519 primitives behave exactly like the Spec model's group
  operations: key generation samples a uniform exponent (`ECKeygenSpec`),
  agreement is scalar multiplication (`ECAgreeSpec`), and every public key is
  canonical (`ECCanonicalSpec`). This is an idealization, not a believed-true
  fact: production X25519 clamps its scalars, `calculate_agreement` rejects
  all-zero shared secrets (so `ECAgreeSpec` fails on low-order inputs), and
  `is_canonical` returns false on non-canonical encodings (so
  `ECCanonicalSpec` is false on adversarial inputs).
* **KEM pairing (`KemPairModel`):** the KEM key generator is assumed to be the
  paired form of the extracted KEM's key generation.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

noncomputable section

variable {Rand SPK SSK S C Msg IdC IdK : Type}

/-- The value of a successful `Result`, or `default` on failure. -/
def getOk {α : Type} [Inhabited α] : Aeneas.Std.Result α → α
  | .ok x => x
  | _ => default

/-- The raw bytes of a curve25519 public key. -/
def pubBytes (p : ECPub) : Key :=
  match p.key with
  | .DjbPublicKey a => a

/-- A curve25519 public key from raw bytes. -/
def pubOfBytes (b : Key) : ECPub := { key := .DjbPublicKey b }

scoped instance : Inhabited ECPub := ⟨pubOfBytes default⟩

/-- View a 32-byte key as a slice. -/
def sliceOfKey (k : Key) : Aeneas.Std.Result (Aeneas.Std.Slice Aeneas.Std.U8) :=
  Aeneas.Std.lift (Aeneas.Std.Array.to_slice k)

/-- View a public key's bytes as a slice. -/
def pubSlice (p : ECPub) : Aeneas.Std.Result (Aeneas.Std.Slice Aeneas.Std.U8) :=
  sliceOfKey (pubBytes p)

/-- A public key from a byte slice, defaulting if the length is wrong. -/
def pubOfSlice (s : Aeneas.Std.Slice Aeneas.Std.U8) : ECPub :=
  pubOfBytes ((toKey s).getD default)

/-- Mirror of the extracted KDF input layout: 32 bytes of 0xFF followed by the
  DH outputs and the KEM secret. -/
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

/-- Run the extracted HKDF derivation on the assembled KDF input. -/
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

/-- The extracted key derivation, split into `(root_key, chain_key,
  pqr_key)`. -/
def deriveKeys (dh1 dh2 dh3 : ECPub) (dh4 : Option ECPub) (ss : Key) :
    Aeneas.Std.Result (Key × Key × Key) := do
  let hk ← deriveHK dh1 dh2 dh3 dh4 ss
  pure (rootKeyBytes hk, chainKeyBytes hk, pqrKeyBytes hk)

/-- Totality of the extracted KDF: `deriveHK` succeeds on every input. -/
def DeriveKeysTotal : Prop :=
  ∀ (dh1 dh2 dh3 : ECPub) (dh4 : Option ECPub) (ss : Key),
    ∃ hk, deriveHK dh1 dh2 dh3 dh4 ss = .ok hk

/-- The extracted ML-KEM encapsulation succeeds on every public key and
  randomness. Unlike the simplified extraction, this depends on the
  parameters' RNG instance, so it is stated over `P` and taken as a
  hypothesis. -/
def EncapsTotalAll (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ (pk : PQPub) (r : Rand),
    ∃ ss ct rest, kem.KeyPublic.encapsulate P.cryptoRngInst pk r = .ok (.Ok (ss, ct), rest)

/-- Curve25519 agreement as a total function on key pairs, defaulting on
  failure; the DH function of the nominal-DDH game. -/
def ecAgree (kp : ECKeyPair) (pk : ECPub) : ECPub :=
  match libsignal_core.curve.PrivateKey.calculate_agreement kp.private_key pk with
  | .ok (.Ok z) => pubOfSlice z
  | _ => default

/-- The Spec-model parameters induced by the extracted primitives; the
  reduction target of the security theorems. -/
def specParams (P : Parameters Rand SPK SSK S C Msg IdC IdK) (F : Type) (gen : ECPub) :
    PQXDH.Parameters F ECPub Key PQPub PQPriv CT SPK SSK S C Msg Key IdC IdK where
  gen := gen
  pqkem := pqkem P
  sig := P.sig
  aead := P.aead
  kdf := fun km => getOk (deriveKeys km.1 km.2.1 km.2.2.1 km.2.2.2.1 km.2.2.2.2)
  idEC := P.idEC
  idKEM := P.idKEM

/-- The extracted KDF modeled as a PRF keyed by the KEM shared secret.
  * MODEL SIMPLIFICATION: mirrors `PQXDH.kdfPRF` in the Spec model. -/
def kdfPRF : PRFScheme Key (ECPub × ECPub × ECPub × Option ECPub) (Key × Key × Key) where
  keygen := $ᵗ Key
  eval := fun ss q => getOk (deriveKeys q.1 q.2.1 q.2.2.1 q.2.2.2 ss)

variable {F : Type}

/-- Package a Spec-model key pair as an extracted key pair, encoding the
  exponent with `privEnc`. -/
def kpOfPair (privEnc : F → ECPriv) (p : ECPub × F) : ECKeyPair where
  public_key := p.1
  private_key := privEnc p.2

/-- The extracted KDF modeled as a PRF keyed by the DH3 slot of the key
  material, with keys sampled as curve25519 key pairs.
  * MODEL SIMPLIFICATION: mirrors `PQXDH.kdfPRFDH` in the Spec model. -/
def kdfPRFDH (P : Parameters Rand SPK SSK S C Msg IdC IdK) :
    PRFScheme ECKeyPair (ECPub × ECPub × Option ECPub × Key) (Key × Key × Key) where
  keygen := P.ecKeygen
  eval := fun kp q => getOk (deriveKeys q.1 q.2.1 kp.public_key q.2.2.1 q.2.2.2)

/-- Package a Spec-model KEM key pair as an extracted KEM key pair. -/
def kpOfKem (pq : PQPub × PQPriv) : PQKeyPair where
  public_key := pq.1
  secret_key := pq.2

/-- Alice's extracted startup parameters induced by their Spec counterpart. -/
def ukOfSpec (privEnc : F → ECPriv)
    (uk : PQXDH.InitiatorParameters F ECPub SPK Msg) :
    InitiatorParameters SPK Msg where
  ikA := identityKeyPairOf (kpOfPair privEnc uk.ikA)
  ikB := { public_key := uk.ikB }
  sigpkB := uk.sigpkB
  msg := uk.msg

/-- Bob's extracted identity induced by its Spec counterpart. -/
def tkOfSpec (privEnc : F → ECPriv)
    (tk : PQXDH.RecipientIdentity F ECPub SPK SSK S) :
    RecipientIdentity SPK SSK S where
  ikB := identityKeyPairOf (kpOfPair privEnc tk.ikB)
  sigkB := tk.sigkB
  spkB := kpOfPair privEnc tk.spkB
  spkSigB := tk.spkSigB

/-- Bob's extracted startup parameters induced by their Spec counterpart. -/
def rpOfSpec (privEnc : F → ECPriv)
    (rp : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S) :
    RecipientParameters SPK SSK S where
  ikB := identityKeyPairOf (kpOfPair privEnc rp.ikB)
  sigkB := rp.sigkB
  spkB := kpOfPair privEnc rp.spkB
  spkSigB := rp.spkSigB
  opkB := rp.opkB.map (kpOfPair privEnc)
  pqpkB := kpOfKem rp.pqpkB

/-- Key generation samples a uniform exponent for `gen`. -/
def ECKeygenSpec [Field F] [SampleableType F]
    [AddCommGroup ECPub] [Module F ECPub]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (gen : ECPub)
    (privEnc : F → ECPriv) : Prop :=
  P.ecKeygen = kpOfPair privEnc <$> PQXDH.dhKeygen (F := F) gen

/-- Agreement is scalar multiplication of the public key by the encoded
  exponent, for every public key. False of production X25519 on low-order
  inputs; see the module docstring. -/
def ECAgreeSpec [Field F] [AddCommGroup ECPub] [Module F ECPub]
    (privEnc : F → ECPriv) : Prop :=
  ∀ (a : F) (pk : ECPub),
    libsignal_core.curve.PrivateKey.calculate_agreement (privEnc a) pk
      = .ok (.Ok (getOk (pubSlice (PQXDH.DH a pk))))

/-- Every public key passes the canonicality check. False of production
  X25519 on non-canonical encodings; see the module docstring. -/
def ECCanonicalSpec : Prop :=
  ∀ pk : ECPub, libsignal_core.curve.PublicKey.is_canonical pk = .ok true

/-- The KEM key generator is the paired form of the extracted KEM's key
  generation. -/
def PQKeygenSpec (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop :=
  P.pqKeygen = kpOfKem <$> (pqkem P).keygen

/-- The clean-group idealization: the opaque curve25519 primitives agree
  pointwise with the Spec model's group operations. See "Model idealizations"
  above. -/
structure ECGroupModel {F : Type} [Field F] [SampleableType F]
    [AddCommGroup ECPub] [Module F ECPub]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (gen : ECPub)
    (privEnc : F → ECPriv) : Prop where
  /-- Key generation samples a uniform exponent; see `ECKeygenSpec`. -/
  keygen_eq : ECKeygenSpec P gen privEnc
  /-- Agreement is scalar multiplication; see `ECAgreeSpec`. -/
  agree_eq : ECAgreeSpec privEnc
  /-- Every public key is canonical; see `ECCanonicalSpec`. -/
  canonical_eq : ECCanonicalSpec

/-- The KEM pairing assumption; see `PQKeygenSpec`. -/
structure KemPairModel (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop where
  /-- The KEM key generator is paired; see `PQKeygenSpec`. -/
  keygen_eq : PQKeygenSpec P

end

end PQXDH.Aeneas.Full
