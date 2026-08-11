/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Simplified.UAKE.Defs

/-!
# Security Definitions for the Simplified Extraction

Definitions that appear in the hypotheses of the top-level security theorems
in `Security.lean`.

Model idealizations
* **Clean-group model (`ECGroupModel`):** the security theorems assume the
  opaque X25519 primitives behave exactly like the Spec model's group
  operations: key generation samples a uniform exponent, agreement is scalar
  multiplication, and every public key is canonical. This is an idealization
  in the style of a DDH analysis, not a believed-true fact about production
  X25519 (which clamps its scalars, rejects low-order agreements, and has
  non-canonical encodings); it is consistent with the demo crate's stubs, but
  not derivable from them.
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace PQXDH.Aeneas.Simplified

noncomputable section

variable {SPK SSK S C Msg IdC IdK : Type} {F : Type}

/-- Package a Spec-model key pair as an extracted `KeyPair`, encoding the
  exponent with `privEnc`. -/
def kpOfPair (privEnc : F → Bytes 32#usize) (p : ECKey × F) : pqxdh.KeyPair where
  private_key := privEnc p.2
  public_key := p.1

/-- The clean-group idealization: the opaque X25519 primitives agree pointwise
  with the Spec model's group operations. See "Model idealizations" above. -/
structure ECGroupModel [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey]
    (P : Parameters SPK SSK S C Msg IdC IdK) (gen : ECKey) (privEnc : F → Bytes 32#usize) :
    Prop where
  /-- Key generation samples a uniform exponent for `gen`. -/
  keygen_eq : P.ecKeygen = kpOfPair privEnc <$> _root_.PQXDH.dhKeygen (F := F) gen
  /-- Agreement is scalar multiplication of the public key by the encoded
    exponent, for every public key. -/
  agree_eq : ∀ (a : F) (pk : ECKey),
    pqxdh.x25519_agree (privEnc a) pk = .ok (_root_.PQXDH.DH a pk)
  /-- Every public key passes the canonicality check. -/
  canonical_eq : ∀ pk : ECKey, pqxdh.ec_is_canonical pk = .ok true

/-- The opaque ML-KEM encapsulation succeeds on every public key and coins.
  Discharged by the believed-true assumption in `Assumptions.lean`. -/
def EncapsTotalAll : Prop :=
  ∀ (pk : PQPK) (coins : Coins), ∃ r, pqxdh.mlkem_encapsulate pk coins = .ok r

end

end PQXDH.Aeneas.Simplified
