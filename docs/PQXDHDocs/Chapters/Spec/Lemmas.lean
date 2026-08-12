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
import PQXDH.Spec.UAKE.CorrectnessLemmas
import PQXDH.Spec.UAKE.WellFormedLemmas
import PQXDH.Spec.UAKE.SecurityLemmas

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

#doc (Manual) "PQXDH Specification Lemmas" =>

:::group "spec_lemmas"
The supporting-lemma layer for the Spec-model theorems.
:::

*This chapter is AI-generated.* It surfaces the supporting-lemma layer of the Spec model (the `*Lemmas.lean` files, whose contents are AI-written) in the blueprint: every declaration appears as its own node, so the blueprint statistics count each supporting lemma individually. The prose is drawn from the doc comments in those files.

# Correctness lemmas

Probability-to-support reductions, round-trip facts for the abstract primitives, and characterizations of the support of an honest protocol run, supporting the correctness theorems.

:::defTitle "spec_lemma_probOutput_probComp_evalDist" "`probOutput_probComp_evalDist`"
:::

::::theorem "spec_lemma_probOutput_probComp_evalDist" (parent := "spec_lemmas") (lean := "PQXDH.probOutput_probComp_evalDist")
Output probabilities under the `probComp` runtime's `evalDist` coincide
with those of the computation itself.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_support_eq_singleton_true_of_evalDist" "`support_eq_singleton_true_of_evalDist`"
:::

::::theorem "spec_lemma_support_eq_singleton_true_of_evalDist" (parent := "spec_lemmas") (lean := "PQXDH.support_eq_singleton_true_of_evalDist")
A Boolean computation that returns `true` with probability 1 has support
`{true}`.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_fst_eq_smul_of_mem_support_dhKeygen" "`fst_eq_smul_of_mem_support_dhKeygen`"
:::

::::theorem "spec_lemma_fst_eq_smul_of_mem_support_dhKeygen" (parent := "spec_lemmas") (lean := "PQXDH.fst_eq_smul_of_mem_support_dhKeygen")
Every key pair produced by `dhKeygen` satisfies `pk = sk • gen`.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_verify_eq_true_of_perfectlyComplete" "`verify_eq_true_of_perfectlyComplete`"
:::

::::theorem "spec_lemma_verify_eq_true_of_perfectlyComplete" (parent := "spec_lemmas") (lean := "PQXDH.verify_eq_true_of_perfectlyComplete")
For a perfectly complete signature scheme, verifying an honestly generated
signature can only return `true`.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_decaps_eq_some_of_perfectlyCorrect" "`decaps_eq_some_of_perfectlyCorrect`"
:::

::::theorem "spec_lemma_decaps_eq_some_of_perfectlyCorrect" (parent := "spec_lemmas") (lean := "PQXDH.decaps_eq_some_of_perfectlyCorrect")
For a perfectly correct KEM, decapsulating an honestly produced ciphertext
can only return the encapsulated shared secret.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_aead_decrypt_encrypt_of_perfectlyCorrect" "`aead_decrypt_encrypt_of_perfectlyCorrect`"
:::

::::theorem "spec_lemma_aead_decrypt_encrypt_of_perfectlyCorrect" (parent := "spec_lemmas") (lean := "PQXDH.aead_decrypt_encrypt_of_perfectlyCorrect")
For a perfectly correct AEAD, decryption inverts encryption under the same
key and associated data.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_mem_support_initiate" "`mem_support_initiate`"
:::

::::theorem "spec_lemma_mem_support_initiate" (parent := "spec_lemmas") (lean := "PQXDH.mem_support_initiate")
Characterization of `initiate` on a pinned, correctly signed bundle: every
outcome is `some`, built from an ephemeral key, an encapsulation, and an
AEAD ciphertext drawn from the corresponding primitives' supports.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_dh_comm" "`dh_comm`"
:::

::::theorem "spec_lemma_dh_comm" (parent := "spec_lemmas") (lean := "PQXDH.dh_comm")
DH agreement commutes on key pairs produced by `dhKeygen`.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_mem_support_accept" "`mem_support_accept`"
:::

::::theorem "spec_lemma_mem_support_accept" (parent := "spec_lemmas") (lean := "PQXDH.mem_support_accept")
Characterization of `accept` when the key identifiers match,
decapsulation yields `ss`, and Alice's ciphertext decrypts: the only outcome
is the session context with the recomputed keys.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_opkB_mem_of_genOPK" "`opkB_mem_of_genOPK`"
:::

::::theorem "spec_lemma_opkB_mem_of_genOPK" (parent := "spec_lemmas") (lean := "PQXDH.opkB_mem_of_genOPK")
Any key pair inside `genOPK`'s optional output is in the support of
`dhKeygen`.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_run_support_initiator" "`run_support_initiator`"
:::

::::theorem "spec_lemma_run_support_initiator" (parent := "spec_lemmas") (lean := "PQXDH.run_support_initiator")
Support characterization of an honest run of the T=Bob scheme: under the
correctness hypotheses, both parties output `some` of the same key, and the
transcript carries exactly the scheme's 3 messages.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_run_support_recipient" "`run_support_recipient`"
:::

::::theorem "spec_lemma_run_support_recipient" (parent := "spec_lemmas") (lean := "PQXDH.run_support_recipient")
Support characterization of an honest run of the T=Alice scheme: under the
correctness hypotheses, both parties output `some` of the same key, and the
transcript carries exactly the scheme's 2 messages.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

# Well-formedness lemmas

Outputs-only-at-completion facts for the party state machines and transcript-length facts for honest runs, supporting the well-formedness theorems.

:::defTitle "spec_lemma_initiator_outputsOnlyAtCompletion" "`initiator_outputsOnlyAtCompletion`"
:::

::::theorem "spec_lemma_initiator_outputsOnlyAtCompletion" (parent := "spec_lemmas") (lean := "PQXDH.initiator_outputsOnlyAtCompletion")
The Spec initiator outputs a key exactly on the states reached by a
completed run: `none` on its initial and mid-handshake states, `some` on
the state installed by a successful `confirm`.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_recipient_outputsOnlyAtCompletion" "`recipient_outputsOnlyAtCompletion`"
:::

::::theorem "spec_lemma_recipient_outputsOnlyAtCompletion" (parent := "spec_lemmas") (lean := "PQXDH.recipient_outputsOnlyAtCompletion")
The Spec recipient outputs a key exactly on the states reached by a
completed run: `none` before accepting, `some` on the state installed by
a successful `accept`.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_initiatorNoConfirm_outputsOnlyAtCompletion" "`initiatorNoConfirm_outputsOnlyAtCompletion`"
:::

::::theorem "spec_lemma_initiatorNoConfirm_outputsOnlyAtCompletion" (parent := "spec_lemmas") (lean := "PQXDH.initiatorNoConfirm_outputsOnlyAtCompletion")
The Spec 2-round initiator outputs a key exactly on the state installed
by a successful `initiate`.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_recipientNoConfirm_outputsOnlyAtCompletion" "`recipientNoConfirm_outputsOnlyAtCompletion`"
:::

::::theorem "spec_lemma_recipientNoConfirm_outputsOnlyAtCompletion" (parent := "spec_lemmas") (lean := "PQXDH.recipientNoConfirm_outputsOnlyAtCompletion")
The Spec 2-round recipient outputs a key exactly on the state installed
by a successful `accept`.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_runHonest_length_initiator" "`runHonest_length_initiator`"
:::

::::theorem "spec_lemma_runHonest_length_initiator" (parent := "spec_lemmas") (lean := "PQXDH.runHonest_length_initiator")
Under the correctness hypotheses, an honest run of the T=Bob parties on
keys drawn from `setup` transfers exactly the scheme's 3 messages.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_runHonest_length_recipient" "`runHonest_length_recipient`"
:::

::::theorem "spec_lemma_runHonest_length_recipient" (parent := "spec_lemmas") (lean := "PQXDH.runHonest_length_recipient")
Under the correctness hypotheses, an honest run of the T=Alice parties
on keys drawn from `setup` transfers exactly the scheme's 2 messages.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

# Security games and events

The challenge-phase game shared by the security hops, the derived experiments (forgery, signature forgery, KEM-key guessing, and the coin-flipped indistinguishability experiment), and the transcript-level event predicates they use.

:::defTitle "spec_lemma_transcriptBundle" "`transcriptBundle`"
:::

::::definition "spec_lemma_transcriptBundle" (parent := "spec_lemmas") (lean := "PQXDH.transcriptBundle")
The pre-key bundle carried by a transcript's first message, if any. In
the T=Bob scheme, a T-oracle session transcript begins with the bundle Bob
published, and a completed challenge transcript begins with the bundle the
initiator accepted (rejected messages are dropped from transcripts).

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_transcriptStart" "`transcriptStart`"
:::

::::definition "spec_lemma_transcriptStart" (parent := "spec_lemmas") (lean := "PQXDH.transcriptStart")
The global-clock timestamp of a transcript's first entry, if any. For a
T-oracle session this is the time the session was opened; for the
challenge transcript it is the time the initiator accepted a bundle.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_oracleBundles" "`oracleBundles`"
:::

::::definition "spec_lemma_oracleBundles" (parent := "spec_lemmas") (lean := "PQXDH.oracleBundles")
The bundles published by the T-oracle sessions, in session order.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_challengeBundle" "`challengeBundle`"
:::

::::definition "spec_lemma_challengeBundle" (parent := "spec_lemmas") (lean := "PQXDH.challengeBundle")
The bundle accepted by the challenge session, if it accepted one.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_honestBundle" "`honestBundle`"
:::

::::definition "spec_lemma_honestBundle" (parent := "spec_lemmas") (lean := "PQXDH.honestBundle")
True if every signed pair the initiator verifies in the bundle `b` was
honestly produced by the challenger: the signed pre-key pair is the one
created by `setup`, and the KEM pair was published by some T-oracle
session. A completed challenge session whose accepted bundle fails this
predicate yields a strong (SUF-CMA) signature forgery.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_pqpkGuessed" "`pqpkGuessed`"
:::

::::definition "spec_lemma_pqpkGuessed" (parent := "spec_lemmas") (lean := "PQXDH.pqpkGuessed")
The KEM-key bad event of the forgery branch: either two T-oracle
sessions published the same KEM public key, or the challenge session
accepted its bundle strictly before some T-oracle session carrying the
same KEM public key was opened (i.e., the adversary predicted an honest
KEM key before it was generated). Both are guessing events on
`P.pqkem.keygen`. No cryptographic hypothesis of the security theorems
excludes them, and a KEM with colliding or predictable public keys
genuinely breaks UAKE security: a second session holding the same KEM key
accepts a replay of the challenge session's initial message, derives the
same session key, and can be revealed without matching the challenge
transcript.

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "spec_lemma_challengePhase" "`challengePhase`"
:::

::::definition "spec_lemma_challengePhase" (parent := "spec_lemmas") (lean := "PQXDH.challengePhase")
The challenge phase of the UAKE experiment against the T=Bob scheme: run
`setup`, then the adversary's challenge stage with oracle access to copies
of T. The challenge bit is independent of this phase, so the experiments
below sample it themselves where needed; this matches `UAKE.Exp` up to
commuting independent samples.

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_exp"}[]
::::

:::defTitle "spec_lemma_forgeExp" "`forgeExp`"
:::

::::definition "spec_lemma_forgeExp" (parent := "spec_lemmas") (lean := "PQXDH.forgeExp")
Forgery experiment: the challenge session completed, but its transcript
matches no T-oracle session, so the adversary spoofed a message from T.

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_exp"}[]
::::

:::defTitle "spec_lemma_forgeProb" "`forgeProb`"
:::

::::definition "spec_lemma_forgeProb" (parent := "spec_lemmas") (lean := "PQXDH.forgeProb")
Probability of the forgery event.

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_exp"}[]
::::

:::defTitle "spec_lemma_sigForgeExp" "`sigForgeExp`"
:::

::::definition "spec_lemma_sigForgeExp" (parent := "spec_lemmas") (lean := "PQXDH.sigForgeExp")
Signature-forgery experiment: the challenge session completed, and some
signed pair in the bundle it accepted was never produced by the
challenger.

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_exp"}[]
::::

:::defTitle "spec_lemma_sigForgeProb" "`sigForgeProb`"
:::

::::definition "spec_lemma_sigForgeProb" (parent := "spec_lemmas") (lean := "PQXDH.sigForgeProb")
Probability of the signature-forgery event.

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_exp"}[]
::::

:::defTitle "spec_lemma_pqpkGuessedExp" "`pqpkGuessedExp`"
:::

::::definition "spec_lemma_pqpkGuessedExp" (parent := "spec_lemmas") (lean := "PQXDH.pqpkGuessedExp")
KEM-key guessing experiment: the bad event `pqpkGuessed` occurred during
the challenge phase.

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_exp"}[]
::::

:::defTitle "spec_lemma_pqpkGuessedProb" "`pqpkGuessedProb`"
:::

::::definition "spec_lemma_pqpkGuessedProb" (parent := "spec_lemmas") (lean := "PQXDH.pqpkGuessedProb")
Probability of the KEM-key guessing event.

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_exp"}[]
::::

:::defTitle "spec_lemma_forgeHonestGoodExp" "`forgeHonestGoodExp`"
:::

::::definition "spec_lemma_forgeHonestGoodExp" (parent := "spec_lemmas") (lean := "PQXDH.forgeHonestGoodExp")
Residual forgery experiment: a forgery on an honestly signed bundle,
with pairwise-distinct and unpredicted KEM keys. This is the event bounded
by the forgery cores (Hop 5).

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_exp"}[]
::::

:::defTitle "spec_lemma_forgeHonestGoodProb" "`forgeHonestGoodProb`"
:::

::::definition "spec_lemma_forgeHonestGoodProb" (parent := "spec_lemmas") (lean := "PQXDH.forgeHonestGoodProb")
Probability of the residual forgery event.

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_exp"}[]
::::

:::defTitle "spec_lemma_indistExp" "`indistExp`"
:::

::::definition "spec_lemma_indistExp" (parent := "spec_lemmas") (lean := "PQXDH.indistExp")
The UAKE experiment with the forgery branch's outright win replaced by a
fair coin flip. Identical to `UAKE.Exp` on the other two branches.

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_exp"}[]
::::

:::defTitle "spec_lemma_indistAdvantage" "`indistAdvantage`"
:::

::::definition "spec_lemma_indistAdvantage" (parent := "spec_lemmas") (lean := "PQXDH.indistAdvantage")
The adversary's advantage over a fair coin in `indistExp`.

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_exp"}[]
::::

# Shared security hops

Hops 1 through 4 of the security proofs, used by both the DH and the PQ security theorems: the forgery/indistinguishability split, the union bound over forgery causes, the SUF-CMA reduction, and the KEM public-key guessing bound.

:::defTitle "spec_lemma_advantage_le_forgeProb_add_indistAdvantage" "`advantage_le_forgeProb_add_indistAdvantage`"
:::

::::theorem "spec_lemma_advantage_le_forgeProb_add_indistAdvantage" (parent := "spec_lemmas") (lean := "PQXDH.advantage_le_forgeProb_add_indistAdvantage")
Hop 1: `UAKE.Exp` and `indistExp` agree except on the forgery branch,
where the former returns `true` and the latter flips a fair coin. After
commuting the challenge bit ahead of the challenge phase, the two
experiments share their sampling prefix, so `UAKE.Exp`'s success
probability lies between `indistExp`'s and `indistExp`'s plus the forgery
probability, and the triangle inequality bounds the UAKE advantage by
`forgeProb` plus `indistAdvantage`. Purely probabilistic; uses no
cryptographic hypotheses.

{usesLabel}`uses` {uses "spec_lemma_forgeProb"}[] · {uses "spec_lemma_indistAdvantage"}[] · {uses "uake_exp"}[]
::::

:::defTitle "spec_lemma_forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood" "`forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood`"
:::

::::theorem "spec_lemma_forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood" (parent := "spec_lemmas") (lean := "PQXDH.forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood")
Hop 2 (union bound): on any completed challenge run, either some signed
pair of the accepted bundle was never produced by the challenger
(`sigForgeExp`), or the KEM-key bad event occurred (`pqpkGuessedExp`), or
the forgery happened with an honest bundle and separated KEM keys
(`forgeHonestGoodExp`). Purely probabilistic; uses no cryptographic
hypotheses.

{usesLabel}`uses` {uses "spec_lemma_forgeProb"}[] · {uses "spec_lemma_sigForgeProb"}[] · {uses "spec_lemma_pqpkGuessedProb"}[] · {uses "spec_lemma_forgeHonestGoodProb"}[]
::::

:::defTitle "spec_lemma_sigForgeProb_le_sig" "`sigForgeProb_le_sig`"
:::

::::theorem "spec_lemma_sigForgeProb_le_sig" (parent := "spec_lemmas") (lean := "PQXDH.sigForgeProb_le_sig")
Hop 3 (SUF-CMA): a signature forgery in the challenge phase yields a
strong existential forgery against `P.sig`.
Intended reduction: the SUF-CMA adversary simulates the challenge phase,
substituting its challenge public key for `sigkB.1` and its signing oracle
for the two uses of `P.sig.sign` (setup's pre-key signature and each
session's KEM-key signature; the signing key is used nowhere else, and the
adversary never sees it). When the challenge session completes, it stops
and outputs the accepted bundle's signed pair that `honestBundle` fails,
so the pair was not returned by any signing query. Determinism of
verification (`hverifyDet`) transfers the initiator's successful
verification of that pair to the SUF-CMA experiment's final check.
Strong unforgeability (rather than EUF-CMA) is needed because `setup` and
`publish` sign only two message forms, so a dishonest bundle may reuse an
honestly signed message with a fresh signature.

{usesLabel}`uses` {uses "spec_lemma_sigForgeProb"}[] · {uses "spec_parameters"}[]
::::

:::defTitle "spec_lemma_pqpkGuessedProb_le" "`pqpkGuessedProb_le`"
:::

::::theorem "spec_lemma_pqpkGuessedProb_le" (parent := "spec_lemmas") (lean := "PQXDH.pqpkGuessedProb_le")
Hop 4 (KEM-key guessing): the bad event `pqpkGuessed` is a union of
pairwise guessing events on `P.pqkem.keygen`, so its probability is
bounded by the number of pairs times the per-pair guessing bound `εpk`.
Intended proof: with at most `q` sessions, the collision part is a union
over at most `q * (q - 1) / 2` unordered session pairs; conditioning on
the earlier key generation, the later one hits it with probability at most
`εpk` by `hpk`. The prediction part is a union over at most `q` pairs of
the accepted bundle and a later-opened session; the accepted bundle's key
is determined strictly before that session's key generation, so `hpk`
applies again. In total `q * (q + 1) / 2 ≤ q ^ 2` pairs (for `q = 0` both
sides vanish).

{usesLabel}`uses` {uses "spec_lemma_pqpkGuessedProb"}[] · {uses "spec_parameters"}[]
::::

# GapDH core hops

Hops 5 and 6 of the DH security theorem: the forgery and indistinguishability cores, against GapDH, the KDF, and the AEAD. These statements are believed true in the current model, but the standard reductions require the KDF to be a programmable random oracle, so their proofs are deferred to that planned model change; the intended sub-hops are recorded in the statements' documentation.

:::defTitle "spec_lemma_forgeHonestGoodProb_le_gap" "`forgeHonestGoodProb_le_gap`"
:::

::::theorem "spec_lemma_forgeHonestGoodProb_le_gap" (parent := "spec_lemmas") (lean := "PQXDH.forgeHonestGoodProb_le_gap")
Hop 5 (forgery core, GapDH): with an honest bundle and separated KEM
keys, a forgery requires breaking GapDH, the KDF, or the AEAD.
Intended proof, as further hops once the KDF is modeled as a random oracle
(see the module comment):
1. Identify the unique T-oracle session that can share the challenge
session's key material: the accepted bundle pins `ikB` (checked by the
initiator), `spkB` (the only EC key `setup` signs), and `pqpkB`
(published by exactly one session, by `hidKEM` and the excluded
collision event).
2. Replace the KDF output triple `(SK, KA, KB)` on the challenge session's
key material with a fresh uniform triple, shared with any T-oracle
session that derives identical key material. A distinguisher must query
the KDF on the challenge key material, whose third DH component is
`DH ekA.2 spkB.1` for the challenge session's fresh ephemeral `ekA`;
embedding the GapDH challenge in `ekA` and `spkB`, recognizing the
query with the DDH oracle, and answering the T oracle's other KDF
queries consistently (again via the DDH oracle) yields a GapDH
adversary. This step consumes `εgap` and, under the current PRF
modeling of the KDF, `εkdf`.
3. With `KA` uniform, an initial message accepted by the paired session
with a modified AEAD ciphertext is a forgery against `KA` (first
`εaead`, via the INT-CTXT-D game whose encryption oracle produces the
challenge session's ciphertext).
4. With `KB` uniform, the confirmation the initiator accepts must have
been produced under `KB` by the paired session (second `εaead`); a
verbatim relay of honestly produced messages forces the global-clock
interleaving of `Matching`, so the transcripts match, contradicting
the forgery event.
The factor `q` is generous (the reduction handles all sessions at once),
but stating the bound with it makes the composed bound collapse to `εsig`
when the adversary opens no sessions, in which case completing the
challenge session already requires a signature forgery.

{usesLabel}`uses` {uses "spec_lemma_forgeHonestGoodProb"}[] · {uses "spec_ddh"}[] · {uses "spec_security_defs"}[]
::::

:::defTitle "spec_lemma_indistAdvantage_le_gap" "`indistAdvantage_le_gap`"
:::

::::theorem "spec_lemma_indistAdvantage_le_gap" (parent := "spec_lemmas") (lean := "PQXDH.indistAdvantage_le_gap")
Hop 6 (indistinguishability core, GapDH): in `indistExp`, the
adversary's guess is better than a fair coin only by breaking GapDH, the
KDF, or the AEAD, or by a KEM public-key collision.
Intended proof, as further hops once the KDF is modeled as a random oracle
(see the module comment):
1. If the challenge session outputs no key, both finalizations hand the
adversary `none` and the guess is independent of the challenge bit, so
it wins with probability exactly `1 / 2`; the coined forgery branch
likewise. Only the ping-pong branch remains.
2. In the ping-pong branch, the accepted bundle equals a T-oracle
session's published bundle (their transcripts match message by
message), so the bundle is honest without a signature hypothesis.
3. Replace the KDF output triple on the challenge session's key material
with a fresh uniform triple, as in the forgery core (`εgap` plus, under
the current PRF modeling, `εkdf`).
4. If the matching session derived different key material (a KEM
decapsulation mismatch), the confirmation the initiator accepted
decrypts under the now-uniform `KB` without having been produced under
it: an AEAD forgery (`εaead`).
5. A reveal query returns the challenge key only for a session with
identical key material. For a session whose transcript matches the
challenge, `fullPingPong` flips a fair coin instead; any other such
session requires two T-oracle sessions sharing a KEM public key.
Both adversary stages together open at most `2 * q` sessions, giving
at most `2 * q ^ 2` pairs and the `2 * q ^ 2 * εpk` term by the
guessing bound (this term also absorbs prediction events in the post
phase, as in Hop 4).
6. Otherwise the challenge key is uniform, independent of the adversary's
view, and unrevealed, so the real and random finalizations are
identically distributed and the guess wins with probability exactly
`1 / 2`.

{usesLabel}`uses` {uses "spec_lemma_indistAdvantage"}[] · {uses "spec_ddh"}[] · {uses "spec_security_defs"}[]
::::

# IND-CCA core hops

Hops 5 and 6 of the PQ security theorem: the forgery and indistinguishability cores, against the KEM's IND-CCA security, the KDF, and the AEAD. Unlike the GapDH cores, these reductions are expressible in the current model; the proofs are deferred as future reduction work.

:::defTitle "spec_lemma_forgeHonestGoodProb_le_pq" "`forgeHonestGoodProb_le_pq`"
:::

::::theorem "spec_lemma_forgeHonestGoodProb_le_pq" (parent := "spec_lemmas") (lean := "PQXDH.forgeHonestGoodProb_le_pq")
Hop 5 (forgery core, IND-CCA): with an honest bundle and separated KEM
keys, a forgery requires breaking the KEM, the KDF, or the AEAD.
Intended proof, as further hops:
1. Identify the unique T-oracle session that can share the challenge
session's key material, as in the GapDH core: the accepted bundle pins
`ikB`, `spkB`, and `pqpkB`, the latter published by exactly one
session by `hidKEM` and the excluded collision event.
2. Guess that session among the at most `q` opened (the factor `q`) and
embed the IND-CCA challenge: its public key becomes the session's
`pqpkB`, the challenge ciphertext and real-or-random secret stand in
for the challenge session's encapsulation, the decapsulation oracle
serves the session's other ciphertexts, and perfect correctness
(`hkemCorrect`) identifies the session's decapsulation of the
challenge ciphertext with the encapsulated secret. This replaces the
challenge session's KEM shared secret with a uniform one (`εkem`).
3. With the KEM secret uniform, `kdfPRF` is a PRF under a hidden uniform
key: routing the challenge session's KDF call, and the paired
session's KDF calls on the challenge ciphertext, through the PRF
oracle replaces their output triples with a shared random function of
the DH tuple (`εkdf`).
4. The AEAD endgame is as in the GapDH core: a tampered initial message
accepted by the paired session forges against `KA`, and an accepted
confirmation not produced by the paired session forges against `KB`
(the two `εaead`); a verbatim relay of honestly produced messages
forces the global-clock interleaving of `Matching`, so the transcripts
match, contradicting the forgery event.
The factor `q` on `εaead` and `εkdf` is generous (only the session guess
needs it), but stating the bound with it makes the composed bound
collapse to the signature term when the adversary opens no sessions.

{usesLabel}`uses` {uses "spec_lemma_forgeHonestGoodProb"}[] · {uses "spec_security_defs"}[]
::::

:::defTitle "spec_lemma_indistAdvantage_le_pq" "`indistAdvantage_le_pq`"
:::

::::theorem "spec_lemma_indistAdvantage_le_pq" (parent := "spec_lemmas") (lean := "PQXDH.indistAdvantage_le_pq")
Hop 6 (indistinguishability core, IND-CCA): in `indistExp`, the
adversary's guess is better than a fair coin only by breaking the KEM or
the KDF, or by a KEM public-key collision.
Intended proof, as further hops:
1. If the challenge session outputs no key, both finalizations hand the
adversary `none` and the guess is independent of the challenge bit, so
it wins with probability exactly `1 / 2`; the coined forgery branch
likewise. Only the ping-pong branch remains.
2. In the ping-pong branch, the accepted bundle equals a T-oracle
session's published bundle, so it is honest without a signature
hypothesis, and the matching session is the paired one.
3. Replace the challenge session's KEM shared secret with a uniform one
by the IND-CCA embedding of the forgery core (`q`, `εkem`). By perfect
correctness the matching session decapsulates the relayed challenge
ciphertext to the same secret, so, unlike the GapDH core, no
decapsulation-mismatch AEAD term arises.
4. Replace the KDF output triple on the challenge session's key material
with a shared random function of the DH tuple (`εkdf`), as in the
forgery core.
5. A reveal query returns the challenge key only for a session with
identical key material. For a session whose transcript matches the
challenge, `fullPingPong` flips a fair coin instead; any other such
session requires two T-oracle sessions sharing a KEM public key.
Both adversary stages together open at most `2 * q` sessions, giving
at most `2 * q ^ 2` pairs and the `2 * q ^ 2 * εpk` term by the
guessing bound (this term also absorbs prediction events in the post
phase, as in Hop 4).
6. Otherwise the challenge key is uniform, independent of the adversary's
view, and unrevealed, so the real and random finalizations are
identically distributed and the guess wins with probability exactly
`1 / 2`.

{usesLabel}`uses` {uses "spec_lemma_indistAdvantage"}[] · {uses "spec_security_defs"}[]
::::

