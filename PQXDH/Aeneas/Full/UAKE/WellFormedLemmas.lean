/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Full.UAKE.SecurityLemmas

/-!
# Well-formedness Lemmas for the High-fidelity Extraction

Supporting lemmas for `WellFormed.lean`: unconditional
outputs-only-at-completion facts for the four extracted parties, and the
`toSpec` simulation lemmas for the 2-round (NoConfirm) parties, which
`SecurityLemmas.lean` does not cover. The proofs in this file are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open libsignal_protocol

namespace PQXDH.Aeneas.Full

noncomputable section

variable {Rand SPK SSK S C Msg IdC IdK : Type}

/-- The extracted initiator outputs a key exactly on the states reached by a
  completed run: `none` on its initial and mid-handshake states, `some` on the
  state installed by a successful `confirm`. -/
lemma initiator_outputsOnlyAtCompletion [DecidableEq Msg]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) :
    (initiator P).OutputsOnlyAtCompletion := by
  unfold Party.OutputsOnlyAtCompletion
  refine ⟨?_, ?_, ?_⟩
  · intro i r hr out hout
    obtain rfl := eq_of_mem_support_pure hr
    exact eq_of_mem_support_pure hout
  · intro st w st' hst' out hout
    rcases st with p | ctx | k
    · rcases w with b | im | conf
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ⟨im', ctx⟩ <;>
          exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · rcases hc : confirm P ctx conf with _ | SK <;>
            simp only [initiator, hc] at hst'
        · exact absurd (eq_of_mem_support_pure hst') (by simp)
        · obtain rfl := Party.StepResult.complete.inj (eq_of_mem_support_pure hst')
          obtain rfl := eq_of_mem_support_pure hout
          simp
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)
  · intro st w st' w' done hst' out hout
    rcases st with p | ctx | k
    · rcases w with b | im | conf
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ⟨im', ctx⟩
        · exact absurd (eq_of_mem_support_pure hst') (by simp)
        · obtain ⟨rfl, -, rfl⟩ :=
            Party.StepResult.acceptAndSend.inj (eq_of_mem_support_pure hst')
          obtain rfl := eq_of_mem_support_pure hout
          simp
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · rcases hc : confirm P ctx conf with _ | SK <;>
            simp only [initiator, hc] at hst' <;>
          exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)

/-- The extracted recipient outputs a key exactly on the states reached by a
  completed run: `none` before accepting, `some` on the state installed by a
  successful `accept`. -/
lemma recipient_outputsOnlyAtCompletion [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    (recipient P hasOPK).OutputsOnlyAtCompletion := by
  unfold Party.OutputsOnlyAtCompletion
  refine ⟨?_, ?_, ?_⟩
  · intro i r hr out hout
    obtain ⟨opkB, -, hr⟩ := support_bind_exists hr
    obtain ⟨pqpkB, -, hr⟩ := support_bind_exists hr
    obtain ⟨bundle, -, hr⟩ := support_bind_exists hr
    obtain rfl := eq_of_mem_support_pure hr
    exact eq_of_mem_support_pure hout
  · intro st w st' hst' out hout
    rcases st with p | k
    · rcases w with b | im | conf
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ctx
        · exact absurd (eq_of_mem_support_pure hst') (by simp)
        · obtain ⟨conf, -, hst'⟩ := support_bind_exists hst'
          exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)
  · intro st w st' w' done hst' out hout
    rcases st with p | k
    · rcases w with b | im | conf
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ctx
        · exact absurd (eq_of_mem_support_pure hst') (by simp)
        · obtain ⟨conf, -, hst'⟩ := support_bind_exists hst'
          obtain ⟨rfl, -, rfl⟩ :=
            Party.StepResult.acceptAndSend.inj (eq_of_mem_support_pure hst')
          obtain rfl := eq_of_mem_support_pure hout
          simp
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)

/-- The extracted 2-round initiator outputs a key exactly on the state
  installed by a successful `initiate`. -/
lemma initiatorNoConfirm_outputsOnlyAtCompletion
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) :
    (initiatorNoConfirm P).OutputsOnlyAtCompletion := by
  unfold Party.OutputsOnlyAtCompletion
  refine ⟨?_, ?_, ?_⟩
  · intro i r hr out hout
    obtain rfl := eq_of_mem_support_pure hr
    exact eq_of_mem_support_pure hout
  · intro st w st' hst' out hout
    rcases st with p | k
    · rcases w with b | im | conf
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ⟨im', ctx⟩ <;>
          exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)
  · intro st w st' w' done hst' out hout
    rcases st with p | k
    · rcases w with b | im | conf
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ⟨im', ctx⟩
        · exact absurd (eq_of_mem_support_pure hst') (by simp)
        · obtain ⟨rfl, -, rfl⟩ :=
            Party.StepResult.acceptAndSend.inj (eq_of_mem_support_pure hst')
          obtain rfl := eq_of_mem_support_pure hout
          simp
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)

/-- The extracted 2-round recipient outputs a key exactly on the state
  installed by a successful `accept`. -/
lemma recipientNoConfirm_outputsOnlyAtCompletion [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters Rand SPK SSK S C Msg IdC IdK) (hasOPK : Bool) :
    (recipientNoConfirm P hasOPK).OutputsOnlyAtCompletion := by
  unfold Party.OutputsOnlyAtCompletion
  refine ⟨?_, ?_, ?_⟩
  · intro i r hr out hout
    obtain ⟨opkB, -, hr⟩ := support_bind_exists hr
    obtain ⟨pqpkB, -, hr⟩ := support_bind_exists hr
    obtain ⟨bundle, -, hr⟩ := support_bind_exists hr
    obtain rfl := eq_of_mem_support_pure hr
    exact eq_of_mem_support_pure hout
  · intro st w st' hst' out hout
    rcases st with p | k
    · rcases w with b | im | conf
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ctx
        · exact absurd (eq_of_mem_support_pure hst') (by simp)
        · obtain rfl := Party.StepResult.complete.inj (eq_of_mem_support_pure hst')
          obtain rfl := eq_of_mem_support_pure hout
          simp
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)
  · intro st w st' w' done hst' out hout
    rcases st with p | k
    · rcases w with b | im | conf
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
      · obtain ⟨r, -, hst'⟩ := support_bind_exists hst'
        rcases r with _ | ctx <;>
          exact absurd (eq_of_mem_support_pure hst') (by simp)
      · exact absurd (eq_of_mem_support_pure hst') (by simp)
    · rcases w with b | im | conf <;>
        exact absurd (eq_of_mem_support_pure hst') (by simp)

section GroupModelBridge

variable {F : Type} [Field F] [SampleableType F] [AddCommGroup ECPub] [Module F ECPub]
  (P : Parameters Rand SPK SSK S C Msg IdC IdK) (gen : ECPub) (privEnc : F → ECPriv)

/-- The extracted 2-round initiator's `init` agrees with the Spec 2-round
  initiator's on converted inputs. -/
lemma initiatorNoConfirm_init_toSpec
    (uk : PQXDH.InitiatorParameters F ECPub SPK Msg) :
    (initiatorNoConfirm P).init (ukOfSpec privEnc uk)
      = Party.InitResult.map (Sum.map (ukOfSpec privEnc) id) <$>
          (PQXDH.initiatorNoConfirm (specParams P F gen)).init uk := by
  simp only [initiatorNoConfirm, PQXDH.initiatorNoConfirm, map_pure,
    Party.InitResult.map, Sum.map_inl]

/-- The extracted 2-round initiator's `step` agrees with the Spec 2-round
  initiator's on converted states. -/
lemma initiatorNoConfirm_step_toSpec
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (hencTotal : EncapsTotalAll P)
    (hkdfTotal : DeriveKeysTotal)
    (st : PQXDH.InitiatorParameters F ECPub SPK Msg ⊕ Key)
    (w : Message ECPub PQPub CT S C IdC IdK) :
    (initiatorNoConfirm P).step (Sum.map (ukOfSpec privEnc) id st) w
      = Party.StepResult.map (Sum.map (ukOfSpec privEnc) id) <$>
          (PQXDH.initiatorNoConfirm (specParams P F gen)).step st w := by
  rcases st with p | k
  · cases w with
    | bundle b =>
        simp only [initiatorNoConfirm, PQXDH.initiatorNoConfirm, Sum.map_inl,
          initiate_toSpec P gen privEnc hkeygen hagree hencTotal hkdfTotal p b, map_bind]
        refine bind_congr fun r => ?_
        rcases r with _ | ⟨im, ctx⟩ <;> simp [Party.StepResult.map]
    | initial im =>
        simp [initiatorNoConfirm, PQXDH.initiatorNoConfirm, Party.StepResult.map]
    | confirmation c =>
        simp [initiatorNoConfirm, PQXDH.initiatorNoConfirm, Party.StepResult.map]
  · cases w <;>
      simp [initiatorNoConfirm, PQXDH.initiatorNoConfirm, Party.StepResult.map]

/-- The extracted 2-round initiator's `output` agrees with the Spec 2-round
  initiator's on converted states. -/
lemma initiatorNoConfirm_output_toSpec
    (st : PQXDH.InitiatorParameters F ECPub SPK Msg ⊕ Key) :
    (initiatorNoConfirm P).output (Sum.map (ukOfSpec privEnc) id st)
      = (PQXDH.initiatorNoConfirm (specParams P F gen)).output st := by
  rcases st with p | k <;> rfl

/-- The extracted 2-round recipient's `init` agrees with the Spec 2-round
  recipient's on converted inputs. -/
lemma recipientNoConfirm_init_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hkeygen : ECKeygenSpec P gen privEnc) (hK : PQKeygenSpec P) (hasOPK : Bool)
    (tk : PQXDH.RecipientIdentity F ECPub SPK SSK S) :
    (recipientNoConfirm P hasOPK).init (tkOfSpec privEnc tk)
      = Party.InitResult.map (Sum.map (rpOfSpec privEnc) id) <$>
          (PQXDH.recipientNoConfirm (specParams P F gen) hasOPK).init tk := by
  unfold PQKeygenSpec at hK
  simp only [recipientNoConfirm, PQXDH.recipientNoConfirm,
    genOPK_toSpec P gen privEnc hkeygen hasOPK, specParams, tkOfSpec, map_bind,
    bind_map_left]
  rw [hK]
  simp only [bind_map_left]
  refine bind_congr fun opkB => ?_
  refine bind_congr fun pqpkB => ?_
  have hrp : (⟨identityKeyPairOf (kpOfPair privEnc tk.ikB), tk.sigkB,
      kpOfPair privEnc tk.spkB, tk.spkSigB, Option.map (kpOfPair privEnc) opkB,
      kpOfKem pqpkB⟩ : RecipientParameters SPK SSK S)
      = rpOfSpec privEnc ⟨tk.ikB, tk.sigkB, tk.spkB, tk.spkSigB, opkB, pqpkB⟩ := rfl
  rw [hrp, publish_toSpec]
  refine bind_congr fun bundle => ?_
  simp [Party.InitResult.map, rpOfSpec]

/-- The extracted 2-round recipient's `step` agrees with the Spec 2-round
  recipient's on converted states. -/
lemma recipientNoConfirm_step_toSpec [DecidableEq IdC] [DecidableEq IdK]
    (hagree : ECAgreeSpec privEnc) (hcanon : ECCanonicalSpec)
    (hkdfTotal : DeriveKeysTotal) (hasOPK : Bool)
    (st : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S ⊕ Key)
    (w : Message ECPub PQPub CT S C IdC IdK) :
    (recipientNoConfirm P hasOPK).step (Sum.map (rpOfSpec privEnc) id st) w
      = Party.StepResult.map (Sum.map (rpOfSpec privEnc) id) <$>
          (PQXDH.recipientNoConfirm (specParams P F gen) hasOPK).step st w := by
  rcases st with rp | k
  · cases w with
    | bundle b =>
        simp [recipientNoConfirm, PQXDH.recipientNoConfirm, Party.StepResult.map]
    | initial im =>
        simp only [recipientNoConfirm, PQXDH.recipientNoConfirm, Sum.map_inl,
          accept_toSpec P gen privEnc hagree hcanon hkdfTotal rp im, map_bind]
        refine bind_congr fun r => ?_
        rcases r with _ | ctx <;> simp [Party.StepResult.map]
    | confirmation c =>
        simp [recipientNoConfirm, PQXDH.recipientNoConfirm, Party.StepResult.map]
  · cases w <;>
      simp [recipientNoConfirm, PQXDH.recipientNoConfirm, Party.StepResult.map]

/-- The extracted 2-round recipient's `output` agrees with the Spec 2-round
  recipient's on converted states. -/
lemma recipientNoConfirm_output_toSpec [DecidableEq IdC] [DecidableEq IdK] (hasOPK : Bool)
    (st : PQXDH.RecipientParameters F ECPub PQPub PQPriv SPK SSK S ⊕ Key) :
    (recipientNoConfirm P hasOPK).output (Sum.map (rpOfSpec privEnc) id st)
      = (PQXDH.recipientNoConfirm (specParams P F gen) hasOPK).output st := by
  rcases st with rp | k <;> rfl

/-- Simulation of the extracted 2-round initiator by the Spec 2-round
  initiator, assembled from the per-component `toSpec` lemmas. -/
lemma initiatorNoConfirm_sim
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (hencTotal : EncapsTotalAll P)
    (hkdfTotal : DeriveKeysTotal) :
    Party.Sim (PQXDH.initiatorNoConfirm (specParams P F gen)) (initiatorNoConfirm P)
      (ukOfSpec privEnc) (Sum.map (ukOfSpec privEnc) id) where
  init_eq := initiatorNoConfirm_init_toSpec P gen privEnc
  step_eq := initiatorNoConfirm_step_toSpec P gen privEnc hkeygen hagree hencTotal hkdfTotal
  output_eq := initiatorNoConfirm_output_toSpec P gen privEnc

/-- Simulation of the extracted 2-round recipient by the Spec 2-round
  recipient, assembled from the per-component `toSpec` lemmas. -/
lemma recipientNoConfirm_sim [DecidableEq IdC] [DecidableEq IdK]
    (hkeygen : ECKeygenSpec P gen privEnc) (hagree : ECAgreeSpec privEnc)
    (hcanon : ECCanonicalSpec) (hK : PQKeygenSpec P)
    (hkdfTotal : DeriveKeysTotal) (hasOPK : Bool) :
    Party.Sim (PQXDH.recipientNoConfirm (specParams P F gen) hasOPK)
      (recipientNoConfirm P hasOPK)
      (tkOfSpec privEnc) (Sum.map (rpOfSpec privEnc) id) where
  init_eq := recipientNoConfirm_init_toSpec P gen privEnc hkeygen hK hasOPK
  step_eq := recipientNoConfirm_step_toSpec P gen privEnc hagree hcanon hkdfTotal hasOPK
  output_eq := recipientNoConfirm_output_toSpec P gen privEnc hasOPK

end GroupModelBridge

end

end PQXDH.Aeneas.Full
