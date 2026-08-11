/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import Verso
import VersoManual
import VersoBlueprint
import PQXDHDocs.Visuals.GameBoxes
import PQXDHDocs.Visuals.AnchorPill
import PQXDH.Aeneas.Simplified.UAKE.CorrectnessLemmas
import PQXDH.Aeneas.Simplified.UAKE.WellFormedLemmas
import PQXDH.Aeneas.Simplified.UAKE.SecurityLemmas

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true
set_option verso.blueprint.foldCodeBlocks true
set_option doc.verso true

#doc (Manual) "Simplified Extraction Lemmas" =>

:::group "aeneas_simplified_lemmas"
The supporting-lemma layer for the simplified extraction's theorems.
:::

*This chapter is AI-generated.* It surfaces the supporting-lemma layer of the simplified extraction (the `*Lemmas.lean` files, whose contents are AI-written) in the blueprint: every declaration appears as its own node, so the blueprint statistics count each supporting lemma individually. The prose is drawn from the doc comments in those files.

# Correctness lemmas

Supporting lemmas for the correctness theorems, characterizing the support of an honest run of the extracted scheme.

:::defTitle "simplified_lemma_probOutput_probComp_evalDist" "`probOutput_probComp_evalDist`"
:::

::::theorem "simplified_lemma_probOutput_probComp_evalDist" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.probOutput_probComp_evalDist")
Output probabilities under the `probComp` runtime's `evalDist` coincide
with those of the computation itself.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "simplified_lemma_support_eq_singleton_true_of_evalDist" "`support_eq_singleton_true_of_evalDist`"
:::

::::theorem "simplified_lemma_support_eq_singleton_true_of_evalDist" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.support_eq_singleton_true_of_evalDist")
A Boolean computation that returns `true` with probability 1 has support
`{true}`.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "simplified_lemma_verify_eq_true_of_perfectlyComplete" "`verify_eq_true_of_perfectlyComplete`"
:::

::::theorem "simplified_lemma_verify_eq_true_of_perfectlyComplete" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.verify_eq_true_of_perfectlyComplete")
For a perfectly complete signature scheme, verifying an honestly generated
signature can only return `true`.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "simplified_lemma_mlkem_decapsulate_eq_ok" "`mlkem_decapsulate_eq_ok`"
:::

::::theorem "simplified_lemma_mlkem_decapsulate_eq_ok" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.mlkem_decapsulate_eq_ok")
For a perfectly correct KEM, the opaque primitives round-trip: if
`mlkem_encapsulate` returns `(ss, ct)` on an honest key pair and honest
coins, then decapsulating `ct` yields `ss`.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "simplified_lemma_aead_decrypt_encrypt_of_perfectlyCorrect" "`aead_decrypt_encrypt_of_perfectlyCorrect`"
:::

::::theorem "simplified_lemma_aead_decrypt_encrypt_of_perfectlyCorrect" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.aead_decrypt_encrypt_of_perfectlyCorrect")
For a perfectly correct AEAD, decryption inverts encryption under the same
key and associated data.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "simplified_lemma_opkB_mem_of_genOPK" "`opkB_mem_of_genOPK`"
:::

::::theorem "simplified_lemma_opkB_mem_of_genOPK" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.opkB_mem_of_genOPK")
Any key pair inside `genOPK`'s optional output is in the support of the
key generator.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "simplified_lemma_pqxdh_accept_eq_of_initiate_eq_ok" "`pqxdh_accept_eq_of_initiate_eq_ok`"
:::

::::theorem "simplified_lemma_pqxdh_accept_eq_of_initiate_eq_ok" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.pqxdh_accept_eq_of_initiate_eq_ok")
The extracted round trip: if `pqxdh_initiate` succeeds, then
`pqxdh_accept` on the matching recipient inputs succeeds with the same
handshake keys, given DH commutativity for each key pair involved, KEM
round-tripping, and canonicality of the ephemeral key.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "simplified_lemma_mem_support_initiate" "`mem_support_initiate`"
:::

::::theorem "simplified_lemma_mem_support_initiate" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.mem_support_initiate")
Characterization of the wrapper `initiate` on a pinned, correctly signed
bundle: every outcome is either `none` (the extracted call failed) or built
from an ephemeral key, coins, a successful `pqxdh_initiate`, and an AEAD
ciphertext from the corresponding supports.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "simplified_lemma_accept_eq_pure_some" "`accept_eq_pure_some`"
:::

::::theorem "simplified_lemma_accept_eq_pure_some" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.accept_eq_pure_some")
The wrapper `accept` is deterministic once the extracted call is pinned:
with matching key identifiers, a successful `pqxdh_accept`, and a decrypting
ciphertext, it returns exactly the resulting session context.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "simplified_lemma_accept_eq_pure_none" "`accept_eq_pure_none`"
:::

::::theorem "simplified_lemma_accept_eq_pure_none" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.accept_eq_pure_none")
The wrapper `accept` rejects whenever the extracted `pqxdh_accept` does
not succeed with keys.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "simplified_lemma_pqxdh_accept_ne_ok_some" "`pqxdh_accept_ne_ok_some`"
:::

::::theorem "simplified_lemma_pqxdh_accept_ne_ok_some" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.pqxdh_accept_ne_ok_some")
The extracted `pqxdh_accept` cannot succeed with keys when the ephemeral
key fails the canonicality check.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "simplified_lemma_run_support_initiator" "`run_support_initiator`"
:::

::::theorem "simplified_lemma_run_support_initiator" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.run_support_initiator")
Support characterization of an honest run of the T=Bob scheme: under the
correctness hypotheses, each party's output is ⊥, or the two outputs
coincide.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "simplified_lemma_run_support_recipient" "`run_support_recipient`"
:::

::::theorem "simplified_lemma_run_support_recipient" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.run_support_recipient")
Support characterization of an honest run of the T=Alice scheme: under the
correctness hypotheses, each party's output is ⊥, or the two outputs
coincide.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_protocol"}[]
::::

# Well-formedness lemmas

Unconditional outputs-only-at-completion facts for the four extracted parties, and the `toSpec` simulation lemmas for the 2-round (NoConfirm) parties, which the security lemmas do not cover.

:::defTitle "simplified_lemma_initiator_outputsOnlyAtCompletion" "`initiator_outputsOnlyAtCompletion`"
:::

::::theorem "simplified_lemma_initiator_outputsOnlyAtCompletion" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.initiator_outputsOnlyAtCompletion")
The extracted initiator outputs a key exactly on the states reached by a
completed run: `none` on its initial and mid-handshake states, `some` on the
state installed by a successful `confirm`.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

:::defTitle "simplified_lemma_recipient_outputsOnlyAtCompletion" "`recipient_outputsOnlyAtCompletion`"
:::

::::theorem "simplified_lemma_recipient_outputsOnlyAtCompletion" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.recipient_outputsOnlyAtCompletion")
The extracted recipient outputs a key exactly on the states reached by a
completed run: `none` before accepting, `some` on the state installed by a
successful `accept`.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

:::defTitle "simplified_lemma_initiatorNoConfirm_outputsOnlyAtCompletion" "`initiatorNoConfirm_outputsOnlyAtCompletion`"
:::

::::theorem "simplified_lemma_initiatorNoConfirm_outputsOnlyAtCompletion" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.initiatorNoConfirm_outputsOnlyAtCompletion")
The extracted 2-round initiator outputs a key exactly on the state
installed by a successful `initiate`.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

:::defTitle "simplified_lemma_recipientNoConfirm_outputsOnlyAtCompletion" "`recipientNoConfirm_outputsOnlyAtCompletion`"
:::

::::theorem "simplified_lemma_recipientNoConfirm_outputsOnlyAtCompletion" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.recipientNoConfirm_outputsOnlyAtCompletion")
The extracted 2-round recipient outputs a key exactly on the state
installed by a successful `accept`.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

:::defTitle "simplified_lemma_initiatorNoConfirm_init_toSpec" "`initiatorNoConfirm_init_toSpec`"
:::

::::theorem "simplified_lemma_initiatorNoConfirm_init_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.initiatorNoConfirm_init_toSpec")
The extracted 2-round initiator's `init` agrees with the Spec 2-round
initiator's on converted inputs.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

:::defTitle "simplified_lemma_initiatorNoConfirm_step_toSpec" "`initiatorNoConfirm_step_toSpec`"
:::

::::theorem "simplified_lemma_initiatorNoConfirm_step_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.initiatorNoConfirm_step_toSpec")
The extracted 2-round initiator's `step` agrees with the Spec 2-round
initiator's on converted states.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

:::defTitle "simplified_lemma_initiatorNoConfirm_output_toSpec" "`initiatorNoConfirm_output_toSpec`"
:::

::::theorem "simplified_lemma_initiatorNoConfirm_output_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.initiatorNoConfirm_output_toSpec")
The extracted 2-round initiator's `output` agrees with the Spec 2-round
initiator's on converted states.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

:::defTitle "simplified_lemma_recipientNoConfirm_init_toSpec" "`recipientNoConfirm_init_toSpec`"
:::

::::theorem "simplified_lemma_recipientNoConfirm_init_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.recipientNoConfirm_init_toSpec")
The extracted 2-round recipient's `init` agrees with the Spec 2-round
recipient's on converted inputs.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

:::defTitle "simplified_lemma_recipientNoConfirm_step_toSpec" "`recipientNoConfirm_step_toSpec`"
:::

::::theorem "simplified_lemma_recipientNoConfirm_step_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.recipientNoConfirm_step_toSpec")
The extracted 2-round recipient's `step` agrees with the Spec 2-round
recipient's on converted states.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

:::defTitle "simplified_lemma_recipientNoConfirm_output_toSpec" "`recipientNoConfirm_output_toSpec`"
:::

::::theorem "simplified_lemma_recipientNoConfirm_output_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.recipientNoConfirm_output_toSpec")
The extracted 2-round recipient's `output` agrees with the Spec 2-round
recipient's on converted states.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

:::defTitle "simplified_lemma_initiatorNoConfirm_sim" "`initiatorNoConfirm_sim`"
:::

::::theorem "simplified_lemma_initiatorNoConfirm_sim" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.initiatorNoConfirm_sim")
Simulation of the extracted 2-round initiator by the Spec 2-round
initiator, assembled from the per-component `toSpec` lemmas.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

:::defTitle "simplified_lemma_recipientNoConfirm_sim" "`recipientNoConfirm_sim`"
:::

::::theorem "simplified_lemma_recipientNoConfirm_sim" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.recipientNoConfirm_sim")
Simulation of the extracted 2-round recipient by the Spec 2-round
recipient, assembled from the per-component `toSpec` lemmas.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

# Security lemmas

The bridge from the extracted scheme to the Spec model: under the clean-group model, each extracted party simulates its Spec counterpart, and the UAKE advantage transports along the simulation.

:::defTitle "simplified_lemma_specParams" "`specParams`"
:::

::::definition "simplified_lemma_specParams" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.specParams")
The Spec-model parameters induced by the extracted primitives; the
reduction target of the security theorems.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_ukOfSpec" "`ukOfSpec`"
:::

::::definition "simplified_lemma_ukOfSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.ukOfSpec")
Alice's extracted startup parameters induced by their Spec counterpart,
encoding private exponents with `privEnc`.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_tkOfSpec" "`tkOfSpec`"
:::

::::definition "simplified_lemma_tkOfSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.tkOfSpec")
Bob's extracted identity induced by its Spec counterpart.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_rpOfSpec" "`rpOfSpec`"
:::

::::definition "simplified_lemma_rpOfSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.rpOfSpec")
Bob's extracted startup parameters induced by their Spec counterpart.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_genOPK_toSpec" "`genOPK_toSpec`"
:::

::::theorem "simplified_lemma_genOPK_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.genOPK_toSpec")
Under the group model, extracted OPK generation is the image of the Spec
model's.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_setup_toSpec" "`setup_toSpec`"
:::

::::theorem "simplified_lemma_setup_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.setup_toSpec")
Under the group model, extracted `setup` is the image of the Spec model's
`setup` under the state conversions.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_publish_toSpec" "`publish_toSpec`"
:::

::::theorem "simplified_lemma_publish_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.publish_toSpec")
Extracted `publish` computes the same bundle as the Spec model's on
converted parameters.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_kpOfPair_public" "`kpOfPair_public`"
:::

::::theorem "simplified_lemma_kpOfPair_public" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.kpOfPair_public")
`kpOfPair` preserves the public key.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_pqxdh_initiate_groupModel" "`pqxdh_initiate_groupModel`"
:::

::::theorem "simplified_lemma_pqxdh_initiate_groupModel" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.pqxdh_initiate_groupModel")
Under the group model, the extracted `pqxdh_initiate` succeeds, its DH
values are the Spec model's, and its handshake keys are the extracted KDF
applied to them.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_pqxdh_accept_groupModel" "`pqxdh_accept_groupModel`"
:::

::::theorem "simplified_lemma_pqxdh_accept_groupModel" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.pqxdh_accept_groupModel")
Under the group model, the extracted `pqxdh_accept` succeeds and computes
the extracted KDF on the Spec model's DH values.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_initiate_toSpec" "`initiate_toSpec`"
:::

::::theorem "simplified_lemma_initiate_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.initiate_toSpec")
Under the group model, the wrapper `initiate` equals the Spec model's
`initiate` on converted parameters, mapped through the state conversions.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_accept_toSpec" "`accept_toSpec`"
:::

::::theorem "simplified_lemma_accept_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.accept_toSpec")
Under the group model, the wrapper `accept` equals the Spec model's
`accept` on converted parameters, mapped through the state conversions.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_confirm_toSpec" "`confirm_toSpec`"
:::

::::theorem "simplified_lemma_confirm_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.confirm_toSpec")
`confirm` agrees with the Spec model's `confirm`.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_initiator_init_toSpec" "`initiator_init_toSpec`"
:::

::::theorem "simplified_lemma_initiator_init_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.initiator_init_toSpec")
The extracted initiator's `init` agrees with the Spec initiator's on
converted inputs.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_initiator_step_toSpec" "`initiator_step_toSpec`"
:::

::::theorem "simplified_lemma_initiator_step_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.initiator_step_toSpec")
The extracted initiator's `step` agrees with the Spec initiator's on
converted states.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_initiator_output_toSpec" "`initiator_output_toSpec`"
:::

::::theorem "simplified_lemma_initiator_output_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.initiator_output_toSpec")
The extracted initiator's `output` agrees with the Spec initiator's on
converted states.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_recipient_init_toSpec" "`recipient_init_toSpec`"
:::

::::theorem "simplified_lemma_recipient_init_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.recipient_init_toSpec")
The extracted recipient's `init` agrees with the Spec recipient's on
converted inputs.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_recipient_step_toSpec" "`recipient_step_toSpec`"
:::

::::theorem "simplified_lemma_recipient_step_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.recipient_step_toSpec")
The extracted recipient's `step` agrees with the Spec recipient's on
converted states.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_recipient_output_toSpec" "`recipient_output_toSpec`"
:::

::::theorem "simplified_lemma_recipient_output_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.recipient_output_toSpec")
The extracted recipient's `output` agrees with the Spec recipient's on
converted states.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_toSpec" "`toSpec`"
:::

::::definition "simplified_lemma_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "AKE.UAKE.Adversary.toSpec")
Reinterpret an adversary against the extracted scheme as one against the
induced Spec scheme; the oracle interfaces coincide.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_opensAtMost_toSpec" "`opensAtMost_toSpec`"
:::

::::theorem "simplified_lemma_opensAtMost_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.opensAtMost_toSpec")
The `openT` query bound transfers to the reinterpreted adversary.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_initiator_sim" "`initiator_sim`"
:::

::::theorem "simplified_lemma_initiator_sim" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.initiator_sim")
Simulation of the extracted initiator by the Spec initiator, assembled
from the per-component `toSpec` lemmas.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_recipient_sim" "`recipient_sim`"
:::

::::theorem "simplified_lemma_recipient_sim" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.recipient_sim")
Simulation of the extracted recipient by the Spec recipient, assembled
from the per-component `toSpec` lemmas.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_exp_toSpec" "`exp_toSpec`"
:::

::::theorem "simplified_lemma_exp_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.exp_toSpec")
Under the group model, the UAKE experiment on the extracted scheme
coincides with the experiment on the induced Spec scheme against the
reinterpreted adversary.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_advantage_toSpec" "`advantage_toSpec`"
:::

::::theorem "simplified_lemma_advantage_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.advantage_toSpec")
Advantage transport: the extracted scheme's UAKE advantage equals the
induced Spec scheme's, for the reinterpreted adversary.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_kdfPRF_specParams" "`kdfPRF_specParams`"
:::

::::theorem "simplified_lemma_kdfPRF_specParams" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.kdfPRF_specParams")
The PRF form of the induced Spec KDF is definitionally the extracted
`kdfPRF`.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_kdfPRFDH_advantage_toSpec" "`kdfPRFDH_advantage_toSpec`"
:::

::::theorem "simplified_lemma_kdfPRFDH_advantage_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.kdfPRFDH_advantage_toSpec")
PRF advantage against the induced Spec DH-keyed KDF equals that against
the extracted one.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_nominalDDHExpReal_toSpec" "`nominalDDHExpReal_toSpec`"
:::

::::theorem "simplified_lemma_nominalDDHExpReal_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.nominalDDHExpReal_toSpec")
The real nominal-DDH experiment against the induced Spec key generation
and DH function coincides with the experiment against the extracted ones.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_nominalDDHExpRand_toSpec" "`nominalDDHExpRand_toSpec`"
:::

::::theorem "simplified_lemma_nominalDDHExpRand_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.nominalDDHExpRand_toSpec")
The random nominal-DDH experiment against the induced Spec key generation
and DH function coincides with the experiment against the extracted ones.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "simplified_lemma_ddh_advantage_toSpec" "`ddh_advantage_toSpec`"
:::

::::theorem "simplified_lemma_ddh_advantage_toSpec" (parent := "aeneas_simplified_lemmas") (lean := "PQXDH.Aeneas.Simplified.ddh_advantage_toSpec")
DDH advantage transport between the extracted and the induced Spec
formulations of the nominal-DDH game.

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

