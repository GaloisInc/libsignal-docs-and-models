/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.UAKE.CorrectnessLemmas
import PQXDH.Aeneas.Full.UAKE.CorrectnessDefs

/-!
# Top-level Correctness Theorems for the High-fidelity Aeneas Extraction

Perfect UAKE correctness for both orientations of the extracted scheme,
mirroring `PQXDH.Spec.UAKE.Correctness`. Correctness needs no group model; the
only assumption about the opaque curve primitives is that X25519 agreement
commutes on honestly generated key pairs (the `AgreeComm` hypothesis). The
`_extractedSig` variants replace the abstract signature-completeness
hypothesis with the `SigModel` hypothesis, discharging completeness via the
extracted signature scheme.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

noncomputable section

variable {Rand SPK SSK S C Msg IdC IdK : Type}

/-- The production extraction in the T=Bob direction has perfect UAKE
  correctness, assuming the KEM and AEAD are perfectly correct, the signature
  is perfectly complete, and X25519 agreement commutes on honest key pairs. -/
theorem uakeInitiator_perfectlyCorrect
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
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

/-- The production extraction in the T=Alice direction has perfect UAKE
  correctness, assuming the KEM and AEAD are perfectly correct, the signature
  is perfectly complete, and X25519 agreement commutes on honest key pairs. -/
theorem uakeRecipient_perfectlyCorrect
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
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

/-- `uakeInitiator_perfectlyCorrect`, with the signature scheme instantiated
  by the extracted XEd25519 implementation via `SigModel`. -/
theorem uakeInitiator_perfectlyCorrect_extractedSig
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand ECPub ECPriv (Aeneas.Std.Slice Aeneas.Std.U8) C Msg IdC IdK)
    (encMsg : ECPub ⊕ PQPub → Aeneas.Std.Slice Aeneas.Std.U8)
    (msg : Msg) (hasOPK : Bool)
    (hsigModel : SigModel P encMsg)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P) :
    UAKE.PerfectlyCorrect (uakeInitiator P msg hasOPK) ProbCompRuntime.probComp := by
  refine uakeInitiator_perfectlyCorrect P msg hasOPK ?_ hkem haead hdh
  rw [hsigModel.sig_eq]
  exact extractedSig_perfectlyComplete _ _ _ hsigModel.keygen_valid _

/-- `uakeRecipient_perfectlyCorrect`, with the signature scheme instantiated
  by the extracted XEd25519 implementation via `SigModel`. -/
theorem uakeRecipient_perfectlyCorrect_extractedSig
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand ECPub ECPriv (Aeneas.Std.Slice Aeneas.Std.U8) C Msg IdC IdK)
    (encMsg : ECPub ⊕ PQPub → Aeneas.Std.Slice Aeneas.Std.U8)
    (msg : Msg) (hasOPK : Bool)
    (hsigModel : SigModel P encMsg)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead)
    (hdh : AgreeComm P) :
    UAKE.PerfectlyCorrect (uakeRecipient P msg hasOPK) ProbCompRuntime.probComp := by
  refine uakeRecipient_perfectlyCorrect P msg hasOPK ?_ hkem haead hdh
  rw [hsigModel.sig_eq]
  exact extractedSig_perfectlyComplete _ _ _ hsigModel.keygen_valid _

end

end PQXDH.Aeneas.Full
