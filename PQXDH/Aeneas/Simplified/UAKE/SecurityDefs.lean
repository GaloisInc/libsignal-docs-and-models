/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Simplified.UAKE.Defs

open OracleSpec OracleComp AKE AKE.UAKE

namespace PQXDH.Aeneas.Simplified

noncomputable section

variable {SPK SSK S C Msg IdC IdK : Type} {F : Type}

def kpOfPair (privEnc : F → Bytes 32#usize) (p : ECKey × F) : pqxdh.KeyPair where
  private_key := privEnc p.2
  public_key := p.1

structure ECGroupModel [Field F] [SampleableType F] [AddCommGroup ECKey] [Module F ECKey]
    (P : Parameters SPK SSK S C Msg IdC IdK) (gen : ECKey) (privEnc : F → Bytes 32#usize) :
    Prop where
  keygen_eq : P.ecKeygen = kpOfPair privEnc <$> _root_.PQXDH.dhKeygen (F := F) gen
  agree_eq : ∀ (a : F) (pk : ECKey),
    pqxdh.x25519_agree (privEnc a) pk = .ok (_root_.PQXDH.DH a pk)
  canonical_eq : ∀ pk : ECKey, pqxdh.ec_is_canonical pk = .ok true

def EncapsTotalAll : Prop :=
  ∀ (pk : PQPK) (coins : Coins), ∃ r, pqxdh.mlkem_encapsulate pk coins = .ok r

end

end PQXDH.Aeneas.Simplified
