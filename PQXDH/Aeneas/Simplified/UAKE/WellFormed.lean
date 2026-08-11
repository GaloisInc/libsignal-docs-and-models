/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Simplified.UAKE.WellFormedLemmas
import PQXDH.Aeneas.Simplified.UAKE.Assumptions
import PQXDH.Spec.UAKE.WellFormedLemmas

/-!
# Well-formedness of the Simplified Extraction's UAKE Schemes

`UAKE.Scheme.WellFormed` for both orientations of the extracted scheme: each
party produces output exactly when its protocol run completes, and an honest
run transfers exactly `rounds` messages. The output conditions are
unconditional facts about the party state machines. The round-count condition
requires every step of an honest run to succeed, which cannot be established
for the opaque primitives without the clean-group idealization; we assume
`ECGroupModel` (as in `Security.lean`) and transfer the honest run to the
Spec model along the party simulations. The supporting lemmas live in
`WellFormedLemmas.lean`.
-/

open OracleSpec OracleComp AKE AKE.UAKE

namespace PQXDH.Aeneas.Simplified

noncomputable section

variable {SPK SSK S C Msg IdC IdK : Type}

/-- The extracted T=Bob scheme is well-formed: both parties output only at
  completion, and an honest run transfers exactly 3 messages.
  * MODEL IDEALIZATION: the round-count condition assumes the clean-group
    model `ECGroupModel` (see `SecurityDefs.lean`), KDF totality, and the
    correctness hypotheses, since an honest run completes only when no opaque
    primitive fails. -/
theorem uakeInitiator_wellFormed
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hGroupModel : ∃ (F : Type) (_ : Field F) (_ : SampleableType F)
      (_ : AddCommGroup ECKey) (_ : Module F ECKey)
      (gen : ECKey) (privEnc : F → Bytes 32#usize),
      ECGroupModel P gen privEnc)
    (hkdfTotal : DeriveKeysTotal)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.Scheme.WellFormed (uakeInitiator P msg hasOPK) := by
  obtain ⟨F, _, _, _, _, gen, privEnc, hM⟩ := hGroupModel
  refine ⟨initiator_outputsOnlyAtCompletion P,
    recipient_outputsOnlyAtCompletion P hasOPK, ?_⟩
  intro uk tk hsetup uOut tOut ms hrun
  replace hsetup : (uk, tk) ∈ support (setup P msg) := hsetup
  replace hrun : (uOut, tOut, ms) ∈ support (Party.runHonest (initiator P)
      (recipient P hasOPK) uk tk (3 + 1)) := hrun
  rw [setup_toSpec P gen privEnc hM msg] at hsetup
  simp only [support_map, Set.mem_image, Prod.exists, Prod.map_apply,
    Prod.mk.injEq] at hsetup
  obtain ⟨uk₀, tk₀, hsetup₀, huk, htk⟩ := hsetup
  subst huk htk
  rw [Party.runHonest_transport (initiator_sim P gen privEnc hM encapsTotalAll hkdfTotal)
    (recipient_sim P gen privEnc hM hkdfTotal hasOPK)] at hrun
  exact _root_.PQXDH.runHonest_length_initiator (specParams P F gen) msg hasOPK hsig hkem
    haead hsetup₀ hrun

/-- The extracted T=Alice scheme is well-formed: both parties output only at
  completion, and an honest run transfers exactly 2 messages.
  * MODEL IDEALIZATION: the round-count condition assumes the clean-group
    model `ECGroupModel` (see `SecurityDefs.lean`), KDF totality, and the
    correctness hypotheses, since an honest run completes only when no opaque
    primitive fails. -/
theorem uakeRecipient_wellFormed
    [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters SPK SSK S C Msg IdC IdK) (msg : Msg) (hasOPK : Bool)
    (hGroupModel : ∃ (F : Type) (_ : Field F) (_ : SampleableType F)
      (_ : AddCommGroup ECKey) (_ : Module F ECKey)
      (gen : ECKey) (privEnc : F → Bytes 32#usize),
      ECGroupModel P gen privEnc)
    (hkdfTotal : DeriveKeysTotal)
    (hsig : P.sig.PerfectlyComplete ProbCompRuntime.probComp)
    (hkem : (pqkem P).PerfectlyCorrect ProbCompRuntime.probComp)
    (haead : AEAD.PerfectlyCorrect P.aead) :
    UAKE.Scheme.WellFormed (uakeRecipient P msg hasOPK) := by
  obtain ⟨F, _, _, _, _, gen, privEnc, hM⟩ := hGroupModel
  refine ⟨recipientNoConfirm_outputsOnlyAtCompletion P hasOPK,
    initiatorNoConfirm_outputsOnlyAtCompletion P, ?_⟩
  intro uk tk hsetup uOut tOut ms hrun
  replace hsetup : (uk, tk) ∈ support (Prod.swap <$> setup P msg) := hsetup
  replace hrun : (uOut, tOut, ms) ∈ support (Party.runHonest (recipientNoConfirm P hasOPK)
      (initiatorNoConfirm P) uk tk (2 + 1)) := hrun
  rw [setup_toSpec P gen privEnc hM msg] at hsetup
  simp only [Functor.map_map, support_map, Set.mem_image, Prod.exists,
    Prod.map_apply, Prod.swap_prod_mk, Prod.mk.injEq] at hsetup
  obtain ⟨uk₀, tk₀, hsetup₀, htk, huk⟩ := hsetup
  subst huk htk
  rw [Party.runHonest_transport (recipientNoConfirm_sim P gen privEnc hM hkdfTotal hasOPK)
    (initiatorNoConfirm_sim P gen privEnc hM encapsTotalAll hkdfTotal)] at hrun
  exact _root_.PQXDH.runHonest_length_recipient (specParams P F gen) msg hasOPK hsig hkem
    haead hsetup₀ hrun

end

end PQXDH.Aeneas.Simplified
