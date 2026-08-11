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
import PQXDH.Aeneas.Full.UAKE.CorrectnessLemmas
import PQXDH.Aeneas.Full.UAKE.WellFormedLemmas
import PQXDH.Aeneas.Full.UAKE.SecurityLemmas

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

#doc (Manual) "High-fidelity Extraction Lemmas" =>

:::group "aeneas_full_lemmas"
The supporting-lemma layer for the high-fidelity extraction's theorems.
:::

*This chapter is AI-generated.* It surfaces the supporting-lemma layer of the high-fidelity extraction (the `*Lemmas.lean` files, whose contents are AI-written) in the blueprint: every declaration appears as its own node, so the blueprint statistics count each supporting lemma individually. The prose is drawn from the doc comments in those files.

# Correctness lemmas

Supporting lemmas for the correctness theorems, characterizing the support of an honest run of the extracted scheme, and deriving completeness of the extracted signature scheme from the assumptions.

:::defTitle "full_lemma_toKey_inj" "`toKey_inj`"
:::

::::theorem "full_lemma_toKey_inj" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.toKey_inj")
`toKey` is injective on successful coercions: slices mapping to the same
32-byte key are equal.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_getRes_eq_some" "`getRes_eq_some`"
:::

::::theorem "full_lemma_getRes_eq_some" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.getRes_eq_some")
`getRes` of a doubly successful extracted call is `some` of its value.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_probOutput_probComp_evalDist" "`probOutput_probComp_evalDist`"
:::

::::theorem "full_lemma_probOutput_probComp_evalDist" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.probOutput_probComp_evalDist")
Output probabilities under the `probComp` runtime's `evalDist` coincide
with those of the computation itself.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_support_eq_singleton_true_of_evalDist" "`support_eq_singleton_true_of_evalDist`"
:::

::::theorem "full_lemma_support_eq_singleton_true_of_evalDist" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.support_eq_singleton_true_of_evalDist")
A Boolean computation that returns `true` with probability 1 has support
`{true}`.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_verify_eq_true_of_perfectlyComplete" "`verify_eq_true_of_perfectlyComplete`"
:::

::::theorem "full_lemma_verify_eq_true_of_perfectlyComplete" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.verify_eq_true_of_perfectlyComplete")
For a perfectly complete signature scheme, verifying an honestly generated
signature can only return `true`.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_aead_decrypt_encrypt_of_perfectlyCorrect" "`aead_decrypt_encrypt_of_perfectlyCorrect`"
:::

::::theorem "full_lemma_aead_decrypt_encrypt_of_perfectlyCorrect" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.aead_decrypt_encrypt_of_perfectlyCorrect")
For a perfectly correct AEAD, decryption inverts encryption under the same
key and associated data.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_opkB_mem_of_genOPK" "`opkB_mem_of_genOPK`"
:::

::::theorem "full_lemma_opkB_mem_of_genOPK" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.opkB_mem_of_genOPK")
Any key pair inside `genOPK`'s optional output is in the support of the
key generator.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_kem_decapsulate_eq_ok" "`kem_decapsulate_eq_ok`"
:::

::::theorem "full_lemma_kem_decapsulate_eq_ok" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.kem_decapsulate_eq_ok")
For a perfectly correct KEM, the extracted primitives round-trip: a
successful `encapsulate` on an honest key pair decapsulates to the same
shared secret.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_from_residual_err_ne" "`from_residual_err_ne`"
:::

::::theorem "full_lemma_from_residual_err_ne" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.from_residual_err_ne")
An error residual never produces a successful result; rules out the
impossible `from_residual` branches when case-splitting extracted code.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_pqxdh_accept_eq_of_initiate_eq_ok" "`pqxdh_accept_eq_of_initiate_eq_ok`"
:::

::::theorem "full_lemma_pqxdh_accept_eq_of_initiate_eq_ok" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.pqxdh_accept_eq_of_initiate_eq_ok")
The extracted round trip: if `pqxdh_initiate` succeeds, then
`pqxdh_accept` on the matching recipient inputs succeeds with the same
handshake keys, given DH commutativity for each key pair involved, KEM
round-tripping, and canonicality of the ephemeral key.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_mem_support_initiate" "`mem_support_initiate`"
:::

::::theorem "full_lemma_mem_support_initiate" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.mem_support_initiate")
Characterization of the wrapper `initiate` on a pinned, correctly signed
bundle: every outcome is either `none` (the extracted call failed) or built
from an ephemeral key, coins, a successful `pqxdh_initiate`, and an AEAD
ciphertext from the corresponding supports.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_accept_eq_pure_some" "`accept_eq_pure_some`"
:::

::::theorem "full_lemma_accept_eq_pure_some" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.accept_eq_pure_some")
The wrapper `accept` is deterministic once the extracted call is pinned:
with matching key identifiers, a successful `pqxdh_accept`, and a decrypting
ciphertext, it returns exactly the resulting session context.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_accept_eq_pure_none" "`accept_eq_pure_none`"
:::

::::theorem "full_lemma_accept_eq_pure_none" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.accept_eq_pure_none")
The wrapper `accept` rejects whenever the extracted `pqxdh_accept` does
not succeed with keys.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_pqxdh_accept_ne_ok_some" "`pqxdh_accept_ne_ok_some`"
:::

::::theorem "full_lemma_pqxdh_accept_ne_ok_some" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.pqxdh_accept_ne_ok_some")
The extracted `pqxdh_accept` cannot succeed with keys when the ephemeral
key fails the canonicality check.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_run_support_initiator" "`run_support_initiator`"
:::

::::theorem "full_lemma_run_support_initiator" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.run_support_initiator")
Support characterization of an honest run of the T=Bob scheme: under the
correctness hypotheses, each party's output is ⊥, or the two outputs
coincide.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_run_support_recipient" "`run_support_recipient`"
:::

::::theorem "full_lemma_run_support_recipient" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.run_support_recipient")
Support characterization of an honest run of the T=Alice scheme: under the
correctness hypotheses, each party's output is ⊥, or the two outputs
coincide.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "full_lemma_extractedSig_perfectlyComplete" "`extractedSig_perfectlyComplete`"
:::

::::theorem "full_lemma_extractedSig_perfectlyComplete" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.extractedSig_perfectlyComplete")
Completeness of the extracted signature scheme, derived from
`extractedSig_signTotal` and `extractedSig_signVerify`: when the key
generator produces valid pairs, sign-then-verify always succeeds.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_protocol"}[]
::::

# Well-formedness lemmas

Unconditional outputs-only-at-completion facts for the four extracted parties, and the `toSpec` simulation lemmas for the 2-round (NoConfirm) parties, which the security lemmas do not cover.

:::defTitle "full_lemma_initiator_outputsOnlyAtCompletion" "`initiator_outputsOnlyAtCompletion`"
:::

::::theorem "full_lemma_initiator_outputsOnlyAtCompletion" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.initiator_outputsOnlyAtCompletion")
The extracted initiator outputs a key exactly on the states reached by a
completed run: `none` on its initial and mid-handshake states, `some` on the
state installed by a successful `confirm`.

{usesLabel}`uses` {uses "aeneas_full_model"}[]
::::

:::defTitle "full_lemma_recipient_outputsOnlyAtCompletion" "`recipient_outputsOnlyAtCompletion`"
:::

::::theorem "full_lemma_recipient_outputsOnlyAtCompletion" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.recipient_outputsOnlyAtCompletion")
The extracted recipient outputs a key exactly on the states reached by a
completed run: `none` before accepting, `some` on the state installed by a
successful `accept`.

{usesLabel}`uses` {uses "aeneas_full_model"}[]
::::

:::defTitle "full_lemma_initiatorNoConfirm_outputsOnlyAtCompletion" "`initiatorNoConfirm_outputsOnlyAtCompletion`"
:::

::::theorem "full_lemma_initiatorNoConfirm_outputsOnlyAtCompletion" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.initiatorNoConfirm_outputsOnlyAtCompletion")
The extracted 2-round initiator outputs a key exactly on the state
installed by a successful `initiate`.

{usesLabel}`uses` {uses "aeneas_full_model"}[]
::::

:::defTitle "full_lemma_recipientNoConfirm_outputsOnlyAtCompletion" "`recipientNoConfirm_outputsOnlyAtCompletion`"
:::

::::theorem "full_lemma_recipientNoConfirm_outputsOnlyAtCompletion" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.recipientNoConfirm_outputsOnlyAtCompletion")
The extracted 2-round recipient outputs a key exactly on the state
installed by a successful `accept`.

{usesLabel}`uses` {uses "aeneas_full_model"}[]
::::

:::defTitle "full_lemma_initiatorNoConfirm_init_toSpec" "`initiatorNoConfirm_init_toSpec`"
:::

::::theorem "full_lemma_initiatorNoConfirm_init_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.initiatorNoConfirm_init_toSpec")
The extracted 2-round initiator's `init` agrees with the Spec 2-round
initiator's on converted inputs.

{usesLabel}`uses` {uses "aeneas_full_model"}[]
::::

:::defTitle "full_lemma_initiatorNoConfirm_step_toSpec" "`initiatorNoConfirm_step_toSpec`"
:::

::::theorem "full_lemma_initiatorNoConfirm_step_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.initiatorNoConfirm_step_toSpec")
The extracted 2-round initiator's `step` agrees with the Spec 2-round
initiator's on converted states.

{usesLabel}`uses` {uses "aeneas_full_model"}[]
::::

:::defTitle "full_lemma_initiatorNoConfirm_output_toSpec" "`initiatorNoConfirm_output_toSpec`"
:::

::::theorem "full_lemma_initiatorNoConfirm_output_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.initiatorNoConfirm_output_toSpec")
The extracted 2-round initiator's `output` agrees with the Spec 2-round
initiator's on converted states.

{usesLabel}`uses` {uses "aeneas_full_model"}[]
::::

:::defTitle "full_lemma_recipientNoConfirm_init_toSpec" "`recipientNoConfirm_init_toSpec`"
:::

::::theorem "full_lemma_recipientNoConfirm_init_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.recipientNoConfirm_init_toSpec")
The extracted 2-round recipient's `init` agrees with the Spec 2-round
recipient's on converted inputs.

{usesLabel}`uses` {uses "aeneas_full_model"}[]
::::

:::defTitle "full_lemma_recipientNoConfirm_step_toSpec" "`recipientNoConfirm_step_toSpec`"
:::

::::theorem "full_lemma_recipientNoConfirm_step_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.recipientNoConfirm_step_toSpec")
The extracted 2-round recipient's `step` agrees with the Spec 2-round
recipient's on converted states.

{usesLabel}`uses` {uses "aeneas_full_model"}[]
::::

:::defTitle "full_lemma_recipientNoConfirm_output_toSpec" "`recipientNoConfirm_output_toSpec`"
:::

::::theorem "full_lemma_recipientNoConfirm_output_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.recipientNoConfirm_output_toSpec")
The extracted 2-round recipient's `output` agrees with the Spec 2-round
recipient's on converted states.

{usesLabel}`uses` {uses "aeneas_full_model"}[]
::::

:::defTitle "full_lemma_initiatorNoConfirm_sim" "`initiatorNoConfirm_sim`"
:::

::::theorem "full_lemma_initiatorNoConfirm_sim" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.initiatorNoConfirm_sim")
Simulation of the extracted 2-round initiator by the Spec 2-round
initiator, assembled from the per-component `toSpec` lemmas.

{usesLabel}`uses` {uses "aeneas_full_model"}[]
::::

:::defTitle "full_lemma_recipientNoConfirm_sim" "`recipientNoConfirm_sim`"
:::

::::theorem "full_lemma_recipientNoConfirm_sim" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.recipientNoConfirm_sim")
Simulation of the extracted 2-round recipient by the Spec 2-round
recipient, assembled from the per-component `toSpec` lemmas.

{usesLabel}`uses` {uses "aeneas_full_model"}[]
::::

# Security lemmas

The bridge from the extracted scheme to the Spec model: under the clean-group and KEM-pairing models, each extracted party simulates its Spec counterpart, and the UAKE advantage transports along the simulation.

:::defTitle "full_lemma_bind_pure_left" "`bind_pure_left`"
:::

::::theorem "full_lemma_bind_pure_left" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.bind_pure_left")
`Result` bind with a pure left operand reduces by application.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_kdfInput_chain" "`kdfInput_chain`"
:::

::::theorem "full_lemma_kdfInput_chain" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.kdfInput_chain")
Folds the KDF-input construction inlined in the extracted code into the
packaged `kdfInput`, transporting a successful derivation across it.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_pubOfBytes_pubBytes" "`pubOfBytes_pubBytes`"
:::

::::theorem "full_lemma_pubOfBytes_pubBytes" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.pubOfBytes_pubBytes")
`pubOfBytes` inverts `pubBytes`.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_pubOfSlice_pubSlice" "`pubOfSlice_pubSlice`"
:::

::::theorem "full_lemma_pubOfSlice_pubSlice" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.pubOfSlice_pubSlice")
`pubOfSlice` inverts `pubSlice`.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_kpOfPair_public" "`kpOfPair_public`"
:::

::::theorem "full_lemma_kpOfPair_public" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.kpOfPair_public")
`kpOfPair` preserves the public key.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_ecAgree_toSpec" "`ecAgree_toSpec`"
:::

::::theorem "full_lemma_ecAgree_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.ecAgree_toSpec")
Under the agreement spec, `ecAgree` on an encoded pair computes the Spec
model's DH function.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_to_slice_of_toKey" "`to_slice_of_toKey`"
:::

::::theorem "full_lemma_to_slice_of_toKey" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.to_slice_of_toKey")
A successful `toKey` coercion round-trips back to the original slice.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_getOk_pubSlice" "`getOk_pubSlice`"
:::

::::theorem "full_lemma_getOk_pubSlice" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.getOk_pubSlice")
`pubSlice` never fails, and its value is the slice of the encoded key
bytes.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_pqxdh_initiate_toKdf" "`pqxdh_initiate_toKdf`"
:::

::::theorem "full_lemma_pqxdh_initiate_toKdf" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.pqxdh_initiate_toKdf")
Runs the extracted `pqxdh_initiate` under the agreement spec: with a
successful encapsulation and a successful derivation on the Spec model's DH
values, it succeeds and returns exactly those handshake keys.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_agree_pubSlice" "`agree_pubSlice`"
:::

::::theorem "full_lemma_agree_pubSlice" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.agree_pubSlice")
The agreement spec, packaged as an existential: `calculate_agreement`
succeeds and its output encodes the Spec model's DH value.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_pqxdh_accept_toKdf" "`pqxdh_accept_toKdf`"
:::

::::theorem "full_lemma_pqxdh_accept_toKdf" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.pqxdh_accept_toKdf")
Runs the extracted `pqxdh_accept` under the agreement and canonicality
specs: with a successful decapsulation and a successful derivation on the
Spec model's DH values, it succeeds and returns exactly those handshake
keys.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_genOPK_toSpec" "`genOPK_toSpec`"
:::

::::theorem "full_lemma_genOPK_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.genOPK_toSpec")
Under the key-generation spec, extracted OPK generation is the image of
the Spec model's.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_setup_toSpec" "`setup_toSpec`"
:::

::::theorem "full_lemma_setup_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.setup_toSpec")
Under the key-generation specs, extracted `setup` is the image of the Spec
model's `setup` under the state conversions.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_publish_toSpec" "`publish_toSpec`"
:::

::::theorem "full_lemma_publish_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.publish_toSpec")
Extracted `publish` computes the same bundle as the Spec model's on
converted parameters.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_initiate_toSpec" "`initiate_toSpec`"
:::

::::theorem "full_lemma_initiate_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.initiate_toSpec")
Under the group-model specs, the wrapper `initiate` equals the Spec
model's `initiate` on converted parameters, mapped through the state
conversions.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_accept_toSpec" "`accept_toSpec`"
:::

::::theorem "full_lemma_accept_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.accept_toSpec")
Under the group-model specs, the wrapper `accept` equals the Spec model's
`accept` on converted parameters, mapped through the state conversions.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_confirm_toSpec" "`confirm_toSpec`"
:::

::::theorem "full_lemma_confirm_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.confirm_toSpec")
`confirm` agrees with the Spec model's `confirm`.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_initiator_init_toSpec" "`initiator_init_toSpec`"
:::

::::theorem "full_lemma_initiator_init_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.initiator_init_toSpec")
The extracted initiator's `init` agrees with the Spec initiator's on
converted inputs.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_initiator_step_toSpec" "`initiator_step_toSpec`"
:::

::::theorem "full_lemma_initiator_step_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.initiator_step_toSpec")
The extracted initiator's `step` agrees with the Spec initiator's on
converted states.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_initiator_output_toSpec" "`initiator_output_toSpec`"
:::

::::theorem "full_lemma_initiator_output_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.initiator_output_toSpec")
The extracted initiator's `output` agrees with the Spec initiator's on
converted states.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_recipient_init_toSpec" "`recipient_init_toSpec`"
:::

::::theorem "full_lemma_recipient_init_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.recipient_init_toSpec")
The extracted recipient's `init` agrees with the Spec recipient's on
converted inputs.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_recipient_step_toSpec" "`recipient_step_toSpec`"
:::

::::theorem "full_lemma_recipient_step_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.recipient_step_toSpec")
The extracted recipient's `step` agrees with the Spec recipient's on
converted states.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_recipient_output_toSpec" "`recipient_output_toSpec`"
:::

::::theorem "full_lemma_recipient_output_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.recipient_output_toSpec")
The extracted recipient's `output` agrees with the Spec recipient's on
converted states.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_toSpecFull" "`toSpecFull`"
:::

::::definition "full_lemma_toSpecFull" (parent := "aeneas_full_lemmas") (lean := "AKE.UAKE.Adversary.toSpecFull")
Reinterpret an adversary against the extracted scheme as one against the
induced Spec scheme; the oracle interfaces coincide.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_opensAtMost_toSpec" "`opensAtMost_toSpec`"
:::

::::theorem "full_lemma_opensAtMost_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.opensAtMost_toSpec")
The `openT` query bound transfers to the reinterpreted adversary.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_initiator_sim" "`initiator_sim`"
:::

::::theorem "full_lemma_initiator_sim" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.initiator_sim")
Simulation of the extracted initiator by the Spec initiator, assembled
from the per-component `toSpec` lemmas.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_recipient_sim" "`recipient_sim`"
:::

::::theorem "full_lemma_recipient_sim" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.recipient_sim")
Simulation of the extracted recipient by the Spec recipient, assembled
from the per-component `toSpec` lemmas.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_exp_toSpec" "`exp_toSpec`"
:::

::::theorem "full_lemma_exp_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.exp_toSpec")
Under the group-model specs, the UAKE experiment on the extracted scheme
coincides with the experiment on the induced Spec scheme against the
reinterpreted adversary.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_advantage_toSpec" "`advantage_toSpec`"
:::

::::theorem "full_lemma_advantage_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.advantage_toSpec")
Advantage transport: the extracted scheme's UAKE advantage equals the
induced Spec scheme's, for the reinterpreted adversary.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_kdfPRF_specParams" "`kdfPRF_specParams`"
:::

::::theorem "full_lemma_kdfPRF_specParams" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.kdfPRF_specParams")
The PRF form of the induced Spec KDF is definitionally the extracted
`kdfPRF`.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_kdfPRFDH_advantage_toSpec" "`kdfPRFDH_advantage_toSpec`"
:::

::::theorem "full_lemma_kdfPRFDH_advantage_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.kdfPRFDH_advantage_toSpec")
PRF advantage against the induced Spec DH-keyed KDF equals that against
the extracted one.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_nominalDDHExpReal_toSpec" "`nominalDDHExpReal_toSpec`"
:::

::::theorem "full_lemma_nominalDDHExpReal_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.nominalDDHExpReal_toSpec")
The real nominal-DDH experiment against the induced Spec key generation
and DH function coincides with the experiment against the extracted ones.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_nominalDDHExpRand_toSpec" "`nominalDDHExpRand_toSpec`"
:::

::::theorem "full_lemma_nominalDDHExpRand_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.nominalDDHExpRand_toSpec")
The random nominal-DDH experiment against the induced Spec key generation
and DH function coincides with the experiment against the extracted ones.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

:::defTitle "full_lemma_ddh_advantage_toSpec" "`ddh_advantage_toSpec`"
:::

::::theorem "full_lemma_ddh_advantage_toSpec" (parent := "aeneas_full_lemmas") (lean := "PQXDH.Aeneas.Full.ddh_advantage_toSpec")
DDH advantage transport between the extracted and the induced Spec
formulations of the nominal-DDH game.

{usesLabel}`uses` {uses "aeneas_full_security_defs"}[]
::::

