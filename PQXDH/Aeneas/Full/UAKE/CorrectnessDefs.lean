/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.UAKE.Assumptions

/-!
# Correctness Definitions for the High-fidelity Aeneas Extraction

Definitions that appear in the hypotheses of the top-level correctness
theorems in `Correctness.lean`.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

noncomputable section

variable {Rand SPK SSK S C Msg IdC IdK : Type}

/-- X25519 agreement commutes on key pairs drawn from `ecKeygen`: the shared
  secret is the same computed from either side. A hypothesis of the
  correctness theorems; it cannot be discharged for an abstract `ecKeygen`. -/
def AgreeComm (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ kp₁ ∈ support P.ecKeygen, ∀ kp₂ ∈ support P.ecKeygen,
    libsignal_core.curve.PrivateKey.calculate_agreement kp₁.private_key kp₂.public_key
      = libsignal_core.curve.PrivateKey.calculate_agreement kp₂.private_key kp₁.public_key

/-- Ties the abstract signature parameter to the extracted implementation:
  `P.sig` is the extracted XEd25519 scheme, and honestly generated key pairs
  are valid. -/
structure SigModel
    (P : Parameters Rand ECPub ECPriv (Aeneas.Std.Slice Aeneas.Std.U8) C Msg IdC IdK)
    (encMsg : ECPub ⊕ PQPub → Aeneas.Std.Slice Aeneas.Std.U8) : Prop where
  /-- `P.sig` is the extracted XEd25519 signature scheme. -/
  sig_eq : P.sig = extractedSig P.rngInst P.cryptoRngInst P.coins P.ecKeygen encMsg
  /-- Every key pair from `ecKeygen` pairs a private key with its derived
    public key. -/
  keygen_valid : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp

end

end PQXDH.Aeneas.Full
