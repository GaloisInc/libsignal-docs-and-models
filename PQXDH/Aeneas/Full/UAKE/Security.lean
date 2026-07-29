/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.UAKE.SecurityLemmas

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

noncomputable section

variable {Rand SPK SSK S C Msg IdC IdK : Type}

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

end

end PQXDH.Aeneas.Full
