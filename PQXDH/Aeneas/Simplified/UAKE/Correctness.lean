/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Simplified.UAKE.CorrectnessLemmas

/-!
# Top-level Correctness Theorems for the Simplified Extraction

Perfect UAKE correctness for both orientations of the extracted scheme,
mirroring `PQXDH.Spec.UAKE.Correctness`. Correctness needs no group model; the
only assumption about the opaque primitives is that X25519 agreement commutes
on honestly generated key pairs (the `AgreeComm` hypothesis).
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace PQXDH.Aeneas.Simplified

noncomputable section

variable {SPK SSK S C Msg IdC IdK : Type}

/-- The simplified extraction in the T=Bob direction has perfect UAKE
  correctness, assuming the KEM and AEAD are perfectly correct, the signature
  is perfectly complete, and X25519 agreement commutes on honest key pairs. -/
theorem uakeInitiator_perfectlyCorrect
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) ProbCompRuntime.probComp := by
  unfold UAKE.PerfectlyCorrect
  rw [probOutput_probComp_evalDist]
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact probFailure_of_liftM_PMF _
  intro b hb
  simp only [UAKE.CorrectExp, uakeInitiator, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, ms, hrun, rfl⟩ := hb
  suffices h : uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join by
    simpa using h
  simp only [setup, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsetup
  obtain ⟨ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, spkSigB, hspkSigB, huk, htk⟩ := hsetup
  subst huk htk
  exact run_support_initiator P hasOPK hsig hkem haead hdh msg hikA hikB hsigkB hspkB
    hspkSigB hrun

/-- The simplified extraction in the T=Alice direction has perfect UAKE
  correctness, assuming the KEM and AEAD are perfectly correct, the signature
  is perfectly complete, and X25519 agreement commutes on honest key pairs. -/
theorem uakeRecipient_perfectlyCorrect
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) ProbCompRuntime.probComp := by
  unfold UAKE.PerfectlyCorrect
  rw [probOutput_probComp_evalDist]
  refine probOutput_eq_one_of_support_subset_singleton ?_ ?_
  · exact probFailure_of_liftM_PMF _
  intro b hb
  simp only [UAKE.CorrectExp, uakeRecipient, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff, Prod.exists] at hb
  obtain ⟨uk, tk, hsetup, uOut, tOut, ms, hrun, rfl⟩ := hb
  suffices h : uOut.join = none ∨ tOut.join = none ∨ uOut.join = tOut.join by
    simpa using h
  simp only [setup, support_map, Set.mem_image, mem_support_bind_iff,
    support_pure, Set.mem_singleton_iff] at hsetup
  obtain ⟨x, ⟨ikA, hikA, ikB, hikB, sigkB, hsigkB, spkB, hspkB, spkSigB, hspkSigB, rfl⟩,
    hswap⟩ := hsetup
  simp only [Prod.swap_prod_mk, Prod.mk.injEq] at hswap
  obtain ⟨huk, htk⟩ := hswap
  subst huk htk
  exact run_support_recipient P hasOPK hsig hkem haead hdh msg hikA hikB hsigkB hspkB
    hspkSigB hrun

end

end PQXDH.Aeneas.Simplified
