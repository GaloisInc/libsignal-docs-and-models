/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.MTP.ICCA.Basic
import VCVio.CryptoFoundations.AsymmEncAlg.INDCCA

open OracleSpec OracleComp

namespace AKE.ICCA

variable {M PK SK C : Type}

def OfAsymmEncAlg (e : AsymmEncAlg ProbComp M PK SK C) : MTP.Scheme ProbComp M PK SK C where
  rounds := 1
  setup := e.keygen
  sender :=
    { State := Unit
      init := fun (pk, m) => do let c ← e.encrypt pk m; pure (.speakFirst () c)
      step := fun _ _ => pure .reject
      output := fun _ => pure (some ()) }
  receiver :=
    { State := SK × Option C
      init := fun sk => pure (.waitForMsg (sk, none))
      step := fun st c => pure (.complete (st.1, some c))
      output := fun st => match st.2 with
        | some c => do let m' ← e.decrypt st.1 c; pure (some m')
        | none => pure none }

theorem OfAsymmEncAlg_correctExp [DecidableEq M] (e : AsymmEncAlg ProbComp M PK SK C) (msg : M) :
    MTP.CorrectExp (OfAsymmEncAlg e) msg = e.CorrectExp msg := by
  sorry

theorem OfAsymmEncAlg_perfectlyCorrect [DecidableEq M] (e : AsymmEncAlg ProbComp M PK SK C)
    (h : e.PerfectlyCorrect ProbCompRuntime.probComp) :
    MTP.PerfectlyCorrect (OfAsymmEncAlg e) := by
  sorry

theorem OfAsymmEncAlg_iCCA_reduces_to_IND_CCA [DecidableEq C]
    (e : AsymmEncAlg ProbComp M PK SK C) (A : Adversary (OfAsymmEncAlg e)) :
    ∃ B : e.IND_CCA_Adversary,
      Pr[= true | Exp A] = Pr[= true | e.IND_CCA_Game ProbCompRuntime.probComp B] := by
  sorry

theorem OfAsymmEncAlg_iCCA_advantage [DecidableEq C]
    (e : AsymmEncAlg ProbComp M PK SK C) (A : Adversary (OfAsymmEncAlg e)) :
    ∃ B : e.IND_CCA_Adversary,
      e.IND_CCA_Advantage ProbCompRuntime.probComp B = 2 * |advantage A| := by
  sorry

end AKE.ICCA
