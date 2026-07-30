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

def AgreeComm (P : Parameters Rand SPK SSK S C Msg IdC IdK) : Prop :=
  ∀ kp₁ ∈ support P.ecKeygen, ∀ kp₂ ∈ support P.ecKeygen,
    libsignal_core.curve.PrivateKey.calculate_agreement kp₁.private_key kp₂.public_key
      = libsignal_core.curve.PrivateKey.calculate_agreement kp₂.private_key kp₁.public_key

structure SigModel
    (P : Parameters Rand ECPub ECPriv (Aeneas.Std.Slice Aeneas.Std.U8) C Msg IdC IdK)
    (encMsg : ECPub ⊕ PQPub → Aeneas.Std.Slice Aeneas.Std.U8) : Prop where
  sig_eq : P.sig = extractedSig P.rngInst P.cryptoRngInst P.coins P.ecKeygen encMsg
  keygen_valid : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp

end

end PQXDH.Aeneas.Full
