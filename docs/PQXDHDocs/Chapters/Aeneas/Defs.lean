import Verso
import VersoManual
import VersoBlueprint
import PQXDHDocs.Visuals.GameBoxes
import PQXDHDocs.Visuals.AnchorPill
import PQXDH.Aeneas.Simplified.UAKE
import PQXDH.Aeneas.Full.UAKE

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

#doc (Manual) "Aeneas-Extracted PQXDH Models" =>

:::group "aeneas"
The Aeneas-extracted PQXDH realizations and their reduction to the spec model.
:::

Two Aeneas extractions of PQXDH are modelled, each realizing the Spec UAKE construction: the *simplified* extraction (`PQXDH.Aeneas.Simplified`) instantiates it with the PQXDH demo crate, and the *high-fidelity* extraction (`PQXDH.Aeneas.Full`) with Signal's production `libsignal_protocol` crate.

# Simplified

The key-agreement orchestration (`pqxdh_initiate`, `pqxdh_accept`, and the KDF input layout) is extracted Rust; the cryptographic primitives (X25519, ML-KEM, HKDF, canonicality checking) are opaque axioms.

*Deviations from a pure "extracted code as UAKE" instantiation*

- **Abstract primitives in `Parameters`.** Key generation, encapsulation coins, the signature scheme, and the AEAD are abstract parameters; the demo crate does not implement them.
- **Wrapper-level protocol steps.** Bob's identity pin, the pre-key signature checks, key identifiers, and both AEAD messages live in the Lean wrappers (`initiate`, `accept`, `confirm`, `recipient`) rather than the extracted Rust.
- **Defaults on failure.** Wrappers coerce `Result` failures of opaque calls to rejections or default values (`pqkem`, `x25519DH`, `kdfPRF`); totality of the opaque calls is tracked by `DeriveKeysTotal` and `EncapsTotalAll`.
- **Bob's extra message.** As in the Spec model, the T=Bob scheme adds a confirmation message from Bob so that T speaks last; see bullet 1 of "Model simplifications" in `PQXDH.Spec.Basic`.

:::defTitle "aeneas_simplified_params" "Simplified extraction parameters"
:::

::::definition "aeneas_simplified_params" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.Parameters")
Constants and primitive cryptographic operations used by the extracted PQXDH. The primitives the demo crate leaves abstract (key generation, encapsulation coins, signatures, AEAD, key identifiers) are parameters here, as in the Spec model.

- `ecKeygen`, `pqKeygen`: generators for X25519 and ML-KEM key pairs.
- `encapsCoins`: randomness source for derandomized encapsulation.
- `sig`: signature scheme used for signing keys.
- `aead`: AEAD used for the protocol's AEAD messages.
- `idEC`, `idKEM`: functions that map DH and KEM public keys to key identifiers.

{usesLabel}`uses` {uses "spec_parameters"}[]
::::

:::defTitle "aeneas_simplified_protocol" "Simplified extraction protocol procedures"
:::

::::definition "aeneas_simplified_protocol" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.deriveKeys, PQXDH.Aeneas.Simplified.pqkem, PQXDH.Aeneas.Simplified.genOPK, PQXDH.Aeneas.Simplified.setup, PQXDH.Aeneas.Simplified.publish, PQXDH.Aeneas.Simplified.initiate, PQXDH.Aeneas.Simplified.accept, PQXDH.Aeneas.Simplified.confirm, PQXDH.Aeneas.Simplified.AgreeComm")
The protocol procedures, wrapping the extracted key agreement.

- `deriveKeys`: the extracted key derivation: build the secret input from the DH outputs and the KEM secret (with or without the OPK), run HKDF, and split the 96-byte output into `(root_key, chain_key, pqr_key)`.
- `pqkem`: the extracted ML-KEM operations packaged as a VCVio KEM scheme. *Not extracted:* encapsulation draws its coins from `encapsCoins`, and both operations coerce failures of the opaque calls to `default` or `none`.
- `setup`: create the long-term state used by Alice and Bob respectively for all sessions; `genOPK` generates a DH OPK only if `hasOPK` is true.
- `publish`: compute Bob's key bundle to send to Alice. *Deviation from spec:* in the spec, this is retrieved by Alice from a third-party server, however in UAKE we have only two parties; therefore, we make this a message from Bob.
- `initiate`: compute Alice's initial message to Bob around the extracted `pqxdh_initiate`. *Not extracted:* Bob's identity pin, the pre-key signature checks, and the AEAD encryption happen in the wrapper; the key agreement itself is extracted code.
- `accept`: Bob's acceptance procedure around the extracted `pqxdh_accept`: check the key identifiers, run the extracted key agreement, and check that Alice's AEAD ciphertext decrypts. Also return the key, message, and AD for Bob's own AEAD ciphertext. *Not extracted:* the identifier checks and the AEAD decryption happen in the wrapper. *Deviation from spec:* Bob's AEAD ciphertext is not present in the spec.
- `confirm`: Alice's confirmation procedure: check if Bob's AEAD ciphertext decrypts with the correct message, AD, and KDF-derived key, and return the shared key, if so.
- `AgreeComm`: X25519 agreement commutes on key pairs drawn from `ecKeygen`: the shared secret is the same computed from either side. A hypothesis of the correctness theorems; it cannot be discharged for an abstract `ecKeygen`.

{usesLabel}`uses` {uses "aeneas_simplified_params"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "aeneas_simplified_model" "Simplified extraction as a UAKE, Bob as T"
:::

::::definition "aeneas_simplified_model" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.uakeInitiator, PQXDH.Aeneas.Simplified.initiator, PQXDH.Aeneas.Simplified.recipient")
UAKE scheme in which Bob plays the part of the authenticated party T and sends a final AEAD ciphertext to match the "T speaks last" convention from DF'17. Alice is the unkeyed party. Three messages are sent: Bob's pre-key bundle, then Alice's initiate message, then Bob's confirmation message.

Alice's Party state machine internally uses the `initiate` function, followed by the `confirm` function, which checks Bob's AEAD ciphertext (not in the spec). Bob's internally uses the `publish` and `accept` functions, as well as sending a final AEAD message (not in the spec).

*Deviation from spec:* UAKE requires T to speak last, sending an authenticated message if the exchange was accepted. This prevents a trivial attack where the attacker simply refrains from sending Alice's last message, so that ping-pong is vacuously false. We have Bob send the final message of the exchange in order to satisfy this, whereas the spec stops at Bob receiving the message.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_uake"}[] · {uses "uake_scheme"}[]
::::

:::defTitle "aeneas_simplified_recipient" "Simplified extraction as a UAKE, Alice as T"
:::

::::definition "aeneas_simplified_recipient" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.uakeRecipient, PQXDH.Aeneas.Simplified.initiatorNoConfirm, PQXDH.Aeneas.Simplified.recipientNoConfirm")
UAKE scheme in which Alice plays the part of the authenticated party T. Bob is the unkeyed party. Two messages are sent: Bob's pre-key bundle, then Alice's initiate message. The party state machines for the 2-round scheme internally use the `initiate`, `publish`, and `accept` functions.

{usesLabel}`uses` {uses "aeneas_simplified_protocol"}[] · {uses "spec_uake_recipient"}[] · {uses "uake_scheme"}[]
::::

:::defTitle "aeneas_simplified_correctness" "Correctness of the simplified extraction, Bob as T"
:::

::::theorem "aeneas_simplified_correctness" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.uakeInitiator_perfectlyCorrect")
The simplified extraction in the T=Bob direction has perfect UAKE correctness, assuming the KEM and AEAD are perfectly correct, the signature is perfectly complete, and X25519 agreement commutes on honest key pairs. Correctness needs no group model; `AgreeComm` is the only assumption about the opaque primitives.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[] · {uses "uake_perfectly_correct"}[]
::::

:::defTitle "aeneas_simplified_recipient_correctness" "Correctness of the simplified extraction, Alice as T"
:::

::::theorem "aeneas_simplified_recipient_correctness" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.uakeRecipient_perfectlyCorrect")
The simplified extraction in the T=Alice direction has perfect UAKE correctness, assuming the KEM and AEAD are perfectly correct, the signature is perfectly complete, and X25519 agreement commutes on honest key pairs.

{usesLabel}`uses` {uses "aeneas_simplified_recipient"}[] · {uses "uake_perfectly_correct"}[]
::::

UAKE security of the extracted scheme is proved by reduction to the Spec theorems: under the group model, the extracted scheme's advantage equals that of the Spec scheme instantiated with the extracted primitives, so the Spec bounds apply.

*Deviations from a pure "extracted code as UAKE" statement*

- **Clean-group model.** Both theorems assume some clean-group model for the opaque X25519 primitives (the `hGroupModel` hypothesis). This is a model idealization, not a believed-true fact.
- **KDF totality.** The `hkdfTotal` hypothesis assumes the extracted KDF never fails.
- **Encapsulation totality.** The proofs use the believed-true assumption `encapsTotalAll`.
- **Inherited Spec simplifications.** The Spec theorems this reduces to are still sorry'd and carry their own simplifications (SUF-CMA signatures, the KDF as a PRF); see the Specification chapter.

:::defTitle "aeneas_simplified_security_defs" "Group model for the simplified extraction"
:::

::::definition "aeneas_simplified_security_defs" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.ECGroupModel, PQXDH.Aeneas.Simplified.EncapsTotalAll, PQXDH.Aeneas.Simplified.kpOfPair, PQXDH.Aeneas.Simplified.DeriveKeysTotal, PQXDH.Aeneas.Simplified.kdfPRF, PQXDH.Aeneas.Simplified.kdfPRFDH, PQXDH.Aeneas.Simplified.x25519DH")
Definitions that appear in the hypotheses of the top-level security theorems.

*Model idealization:* the security theorems assume the opaque X25519 primitives behave exactly like the Spec model's group operations: key generation samples a uniform exponent, agreement is scalar multiplication, and every public key is canonical (`ECGroupModel`). This is an idealization in the style of a DDH analysis, not a believed-true fact about production X25519 (which clamps its scalars, rejects low-order agreements, and has non-canonical encodings); it is consistent with the demo crate's stubs, but not derivable from them.

`EncapsTotalAll` states that the opaque ML-KEM encapsulation succeeds on every public key and coins, and `DeriveKeysTotal` that the extracted KDF succeeds on every input. `kdfPRF` and `kdfPRFDH` model the extracted KDF as a PRF, keyed by the KEM shared secret or by the DH3 slot of the key material, mirroring the Spec model.

{usesLabel}`uses` {uses "aeneas_simplified_params"}[]
::::

:::defTitle "aeneas_simplified_assumptions" "Assumptions about the simplified extraction"
:::

::::definition "aeneas_simplified_assumptions" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.encapsTotalAll")
Facts about the Rust implementation that appear to be true, but which are unprovable here due to gaps in the code model extracted by Aeneas. For the simplified extraction there is one: encapsulation totality. True of the Rust, not provable here: the demo crate declares `mlkem_encapsulate` as a `charon::opaque` native with an infallible signature, so encapsulation always returns a value; the `Result` on the extracted axiom exists only because Aeneas conservatively wraps every opaque call in `Result`. We cannot derive totality here because the axiom has no body.

:::leanPill "partial"
:::

{usesLabel}`uses` {uses "aeneas_simplified_security_defs"}[]
::::

:::defTitle "aeneas_simplified_reduction" "Reduction of the simplified extraction to the spec"
:::

::::theorem "aeneas_simplified_reduction" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.advantage_toSpec")
The bridge from the extracted scheme to the Spec model: under the clean-group model, each extracted party simulates its Spec counterpart, and the UAKE advantage transports along the simulation.

{usesLabel}`uses` {uses "aeneas_simplified_model"}[] · {uses "aeneas_simplified_security_defs"}[] · {uses "spec_uake"}[]
::::

:::defTitle "aeneas_simplified_security" "Security of the simplified extraction, PQ setting"
:::

::::theorem "aeneas_simplified_security" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.uakeInitiator_secure_pq")
Top-level UAKE security theorem for the simplified extraction, making no assumptions about the underlying DH key exchange, but assuming the KEM is secure. This models UAKE security in the PQ setting: the adversary's advantage in the UAKE game is bounded as a polynomial over the adversary bounds of the underlying schemes, where the coefficients are small constants and the number $`q` of sessions started with its T oracle.

:::leanPill "partial"
:::

{usesLabel}`uses` {uses "aeneas_simplified_reduction"}[] · {uses "aeneas_simplified_assumptions"}[] · {uses "spec_uake_security"}[]
::::

:::defTitle "aeneas_simplified_security_dh" "Security of the simplified extraction, non-PQ setting"
:::

::::theorem "aeneas_simplified_security_dh" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.uakeInitiator_secure_dh")
Top-level UAKE security theorem for the simplified extraction, assuming the underlying DH key exchange is hard to break. This models UAKE security in the non-PQ setting: the adversary's advantage in the UAKE game is bounded as a polynomial over the adversary bounds of the underlying schemes, where the coefficients are small constants and the number $`q` of sessions started with its T oracle.

:::leanPill "partial"
:::

{usesLabel}`uses` {uses "aeneas_simplified_reduction"}[] · {uses "aeneas_simplified_assumptions"}[] · {uses "spec_uake_security"}[]
::::

# Full

This realization uses Signal's production `libsignal_protocol` crate, as extracted by Aeneas. The protocol orchestration (`pqxdh_initiate`, `pqxdh_accept`, key derivation) is extracted Rust; the cryptographic primitives (curve25519, ML-KEM, HKDF internals) remain opaque axioms.

*Deviations from a pure "extracted code as UAKE" instantiation*

- **Abstract primitives in `Parameters`.** Key generation, the randomness source, the signature scheme, and the AEAD are abstract parameters. The extracted signature scheme is packaged separately (`extractedSig`) and tied to `sig` by the correctness theorems' `SigModel` hypothesis.
- **Wrapper-level protocol steps.** Bob's identity pin, the pre-key signature checks, key identifiers, and both AEAD messages live in the Lean wrappers (`initiate`, `accept`, `confirm`, `recipient`) rather than the extracted Rust.
- **Randomness threading.** The extracted functions take an explicit RNG; the wrappers (`runRaw`, `runRes`) sample it from `coins` and coerce failures to `none`.
- **Byte-length coercions.** The extraction does not track slice lengths, so 32-byte keys are recovered with `toKey`.
- **Bob's extra message.** As in the Spec model, the T=Bob scheme adds a confirmation message from Bob so that T speaks last; see bullet 1 of "Model simplifications" in `PQXDH.Spec.Basic`.

:::defTitle "aeneas_full_params" "High-fidelity extraction parameters"
:::

::::definition "aeneas_full_params" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.Parameters")
Constants and primitive cryptographic operations used by the extracted PQXDH. Operations the extraction leaves abstract (randomness, key generation, signatures, AEAD, key identifiers) are parameters here, as in the Spec model.

- `rngInst`, `cryptoRngInst`: the extracted code's RNG instances.
- `coins`: distribution of the explicit randomness threaded through extracted calls.
- `ecKeygen`, `pqKeygen`: generators for curve25519 and ML-KEM key pairs.
- `sig`: signature scheme used for signing keys; instantiated with `extractedSig` by the `SigModel` hypothesis.
- `aead`: AEAD used for the protocol's AEAD messages.
- `idEC`, `idKEM`: functions that map DH and KEM public keys to key identifiers.

{usesLabel}`uses` {uses "spec_parameters"}[]
::::

:::defTitle "aeneas_full_protocol" "High-fidelity extraction protocol procedures"
:::

::::definition "aeneas_full_protocol" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.runRaw, PQXDH.Aeneas.Full.runRes, PQXDH.Aeneas.Full.toKey, PQXDH.Aeneas.Full.pqkem, PQXDH.Aeneas.Full.extractedSig, PQXDH.Aeneas.Full.ECKeyPairValid, PQXDH.Aeneas.Full.genOPK, PQXDH.Aeneas.Full.setup, PQXDH.Aeneas.Full.publish, PQXDH.Aeneas.Full.initiate, PQXDH.Aeneas.Full.accept, PQXDH.Aeneas.Full.confirm")
The protocol procedures, wrapping the extracted key agreement.

- `runRaw`, `runRes`: run an extracted RNG-threading computation on randomness from `coins`, coercing failure to `none`.
- `toKey`: coerce a byte slice to a 32-byte key, or `none` if the length differs. *Not extracted:* the extraction does not track slice lengths, so this check is wrapper-level.
- `pqkem`: the extracted ML-KEM operations packaged as a VCVio KEM scheme. *Not extracted:* encapsulation draws randomness from `coins`, shared secrets are coerced to 32-byte keys with `toKey`, and failures are coerced to `default` or `none`.
- `extractedSig`: the extracted XEd25519 signature scheme packaged as a VCVio signature scheme. *Not extracted:* signing draws randomness from `coins` and coerces failure to `default`; verification coerces failure to `false`.
- `ECKeyPairValid`: a key pair is valid when its public half is derived from its private half. `curve.KeyPair` is a plain struct, so this is not automatic.
- `setup`: create the long-term state used by Alice and Bob respectively for all sessions; `genOPK` generates a DH OPK only if `hasOPK` is true.
- `publish`: compute Bob's key bundle to send to Alice. *Deviation from spec:* in the spec, this is retrieved by Alice from a third-party server, however in UAKE we have only two parties; therefore, we make this a message from Bob.
- `initiate`: compute Alice's initial message to Bob around the extracted `pqxdh_initiate`. *Not extracted:* Bob's identity pin, the pre-key signature checks, and the AEAD encryption happen in the wrapper; the key agreement itself is extracted code.
- `accept`: Bob's acceptance procedure around the extracted `pqxdh_accept`: check the key identifiers, run the extracted key agreement, and check that Alice's AEAD ciphertext decrypts. Also return the key, message, and AD for Bob's own AEAD ciphertext. *Not extracted:* the identifier checks and the AEAD decryption happen in the wrapper. *Deviation from spec:* Bob's AEAD ciphertext is not present in the spec.
- `confirm`: Alice's confirmation procedure: check if Bob's AEAD ciphertext decrypts with the correct message, AD, and KDF-derived key, and return the shared key, if so.

{usesLabel}`uses` {uses "aeneas_full_params"}[] · {uses "spec_protocol"}[]
::::

:::defTitle "aeneas_full_model" "High-fidelity extraction as a UAKE, Bob as T"
:::

::::definition "aeneas_full_model" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.uakeInitiator, PQXDH.Aeneas.Full.initiator, PQXDH.Aeneas.Full.recipient")
UAKE scheme in which Bob plays the part of the authenticated party T and sends a final AEAD ciphertext to match the "T speaks last" convention from DF'17. Alice is the unkeyed party. Three messages are sent: Bob's pre-key bundle, then Alice's initiate message, then Bob's confirmation message.

Alice's Party state machine internally uses the `initiate` function, followed by the `confirm` function, which checks Bob's AEAD ciphertext (not in the spec). Bob's internally uses the `publish` and `accept` functions, as well as sending a final AEAD message (not in the spec).

*Deviation from spec:* UAKE requires T to speak last, sending an authenticated message if the exchange was accepted. This prevents a trivial attack where the attacker simply refrains from sending Alice's last message, so that ping-pong is vacuously false. We have Bob send the final message of the exchange in order to satisfy this, whereas the spec stops at Bob receiving the message.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_uake"}[] · {uses "uake_scheme"}[]
::::

:::defTitle "aeneas_full_recipient" "High-fidelity extraction as a UAKE, Alice as T"
:::

::::definition "aeneas_full_recipient" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.uakeRecipient, PQXDH.Aeneas.Full.initiatorNoConfirm, PQXDH.Aeneas.Full.recipientNoConfirm")
UAKE scheme in which Alice plays the part of the authenticated party T. Bob is the unkeyed party. Two messages are sent: Bob's pre-key bundle, then Alice's initiate message. The party state machines for the 2-round scheme internally use the `initiate`, `publish`, and `accept` functions.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[] · {uses "spec_uake_recipient"}[] · {uses "uake_scheme"}[]
::::

:::defTitle "aeneas_full_assumptions" "Assumptions about the high-fidelity extraction"
:::

::::definition "aeneas_full_assumptions" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.encaps_toKey_isSome, PQXDH.Aeneas.Full.decaps_toKey_isSome, PQXDH.Aeneas.Full.as_ref_eq_ok, PQXDH.Aeneas.Full.extractedSig_signVerify, PQXDH.Aeneas.Full.extractedSig_signTotal")
Facts about the Rust implementation that appear to be true, but which are unprovable here due to gaps in the code model extracted by Aeneas.

- `encaps_toKey_isSome`, `decaps_toKey_isSome`: ML-KEM shared secrets are 32 bytes (FIPS 203), so `toKey` never fails on them, but the KEM bottoms out in opaque axioms whose types constrain no lengths. Discharging these needs a length-refined model of those axioms, or extraction of the implementation.
- `as_ref_eq_ok`: Aeneas erases `Box<T>` to `T`, so `Box::as_ref` can only be the identity; it is an axiom rather than a definition because the extraction's external-model file supplies no body. A modelling stub, not a knowledge gap: giving that axiom its evident model would discharge it outright.
- `extractedSig_signVerify`: XEd25519 sign-then-verify agreement: a signature produced by `calculate_signature` verifies under the public key derived from the same private key. The `ECKeyPairValid` premise is necessary, not incidental: `curve.KeyPair` is a plain struct, and Rust's `KeyPair::new` and `from_public_and_private` build one from unrelated halves, so without it the statement is false.
- `extractedSig_signTotal`: signing always succeeds, for every signing key, message, and randomness; no validity premise is needed. `calculate_signature_for_multipart_message` matches on `PrivateKeyData`, which has a single variant, and returns `Ok(..)` unconditionally; its `Result` is vestigial.

:::leanPill "partial"
:::

{usesLabel}`uses` {uses "aeneas_full_protocol"}[]
::::

:::defTitle "aeneas_full_correctness_defs" "Correctness hypotheses for the high-fidelity extraction"
:::

::::definition "aeneas_full_correctness_defs" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.AgreeComm, PQXDH.Aeneas.Full.SigModel")
Definitions that appear in the hypotheses of the top-level correctness theorems.

- `AgreeComm`: X25519 agreement commutes on key pairs drawn from `ecKeygen`: the shared secret is the same computed from either side. A hypothesis of the correctness theorems; it cannot be discharged for an abstract `ecKeygen`.
- `SigModel`: ties the abstract signature parameter to the extracted implementation: `sig` is the extracted XEd25519 scheme, and honestly generated key pairs are valid.

{usesLabel}`uses` {uses "aeneas_full_protocol"}[]
::::

:::defTitle "aeneas_full_correctness" "Correctness of the high-fidelity extraction, Bob as T"
:::

::::theorem "aeneas_full_correctness" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.uakeInitiator_perfectlyCorrect, PQXDH.Aeneas.Full.uakeInitiator_perfectlyCorrect_extractedSig")
The high-fidelity extraction in the T=Bob direction has perfect UAKE correctness, assuming the KEM and AEAD are perfectly correct, the signature is perfectly complete, and X25519 agreement commutes on honest key pairs. The `_extractedSig` variant replaces the abstract signature-completeness hypothesis with the `SigModel` hypothesis, discharging completeness via the extracted signature scheme.

{usesLabel}`uses` {uses "aeneas_full_model"}[] · {uses "aeneas_full_correctness_defs"}[] · {uses "aeneas_full_assumptions"}[] · {uses "uake_perfectly_correct"}[]
::::

:::defTitle "aeneas_full_recipient_correctness" "Correctness of the high-fidelity extraction, Alice as T"
:::

::::theorem "aeneas_full_recipient_correctness" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.uakeRecipient_perfectlyCorrect, PQXDH.Aeneas.Full.uakeRecipient_perfectlyCorrect_extractedSig")
The high-fidelity extraction in the T=Alice direction has perfect UAKE correctness, assuming the KEM and AEAD are perfectly correct, the signature is perfectly complete, and X25519 agreement commutes on honest key pairs. The `_extractedSig` variant replaces the abstract signature-completeness hypothesis with the `SigModel` hypothesis, discharging completeness via the extracted signature scheme.

{usesLabel}`uses` {uses "aeneas_full_recipient"}[] · {uses "aeneas_full_correctness_defs"}[] · {uses "aeneas_full_assumptions"}[] · {uses "uake_perfectly_correct"}[]
::::

UAKE security of the extracted scheme is proved by reduction to the Spec theorems: under the group and KEM-pairing models, the extracted scheme's advantage equals that of the Spec scheme instantiated with the extracted primitives, so the Spec bounds apply.

*Deviations from a pure "extracted code as UAKE" statement*

- **Clean-group model.** Both theorems assume some clean-group model for the opaque curve25519 primitives (the `hGroupModel` hypothesis). This is a model idealization, not a believed-true fact.
- **KEM pairing.** The `hK` hypothesis assumes the KEM key generator is the paired form of the extracted KEM's key generation.
- **Totality hypotheses.** `hencTotal` assumes the extracted encapsulation never fails, and `hkdfTotal` assumes the extracted KDF never fails.
- **Inherited Spec simplifications.** The Spec theorems this reduces to are still sorry'd and carry their own simplifications (SUF-CMA signatures, the KDF as a PRF); see the Specification chapter.

:::defTitle "aeneas_full_security_defs" "Group and KEM models for the high-fidelity extraction"
:::

::::definition "aeneas_full_security_defs" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.ECGroupModel, PQXDH.Aeneas.Full.KemPairModel, PQXDH.Aeneas.Full.ECKeygenSpec, PQXDH.Aeneas.Full.ECAgreeSpec, PQXDH.Aeneas.Full.ECCanonicalSpec, PQXDH.Aeneas.Full.PQKeygenSpec, PQXDH.Aeneas.Full.EncapsTotalAll, PQXDH.Aeneas.Full.DeriveKeysTotal, PQXDH.Aeneas.Full.deriveKeys, PQXDH.Aeneas.Full.specParams, PQXDH.Aeneas.Full.kdfPRF, PQXDH.Aeneas.Full.kdfPRFDH")
Definitions that appear in the hypotheses of the top-level security theorems, together with the Lean-level mirror of the extracted KDF and the packaging of the extracted primitives as Spec-model parameters (`specParams`).

*Model idealizations*

- **Clean-group model (`ECGroupModel`).** The security theorems assume the opaque curve25519 primitives behave exactly like the Spec model's group operations: key generation samples a uniform exponent (`ECKeygenSpec`), agreement is scalar multiplication (`ECAgreeSpec`), and every public key is canonical (`ECCanonicalSpec`). This is an idealization, not a believed-true fact: production X25519 clamps its scalars, `calculate_agreement` rejects all-zero shared secrets (so `ECAgreeSpec` fails on low-order inputs), and `is_canonical` returns false on non-canonical encodings (so `ECCanonicalSpec` is false on adversarial inputs).
- **KEM pairing (`KemPairModel`).** The KEM key generator is assumed to be the paired form of the extracted KEM's key generation (`PQKeygenSpec`).

`EncapsTotalAll` states that the extracted ML-KEM encapsulation succeeds on every public key and randomness; unlike the simplified extraction, this depends on the parameters' RNG instance, so it is stated over the parameters and taken as a hypothesis. `DeriveKeysTotal` states that the extracted KDF succeeds on every input. `kdfPRF` and `kdfPRFDH` model the extracted KDF as a PRF, keyed by the KEM shared secret or by the DH3 slot of the key material, mirroring the Spec model.

{usesLabel}`uses` {uses "aeneas_full_params"}[]
::::

:::defTitle "aeneas_full_reduction" "Reduction of the high-fidelity extraction to the spec"
:::

::::theorem "aeneas_full_reduction" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.advantage_toSpec")
The bridge from the extracted scheme to the Spec model: under the clean-group and KEM-pairing models, each extracted party simulates its Spec counterpart, and the UAKE advantage transports along the simulation.

{usesLabel}`uses` {uses "aeneas_full_model"}[] · {uses "aeneas_full_security_defs"}[] · {uses "spec_uake"}[]
::::

:::defTitle "aeneas_full_security" "Security of the high-fidelity extraction, PQ setting"
:::

::::theorem "aeneas_full_security" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.uakeInitiator_secure_pq")
Top-level UAKE security theorem for the high-fidelity extraction, making no assumptions about the underlying DH key exchange, but assuming the KEM is secure. This models UAKE security in the PQ setting: the adversary's advantage in the UAKE game is bounded as a polynomial over the adversary bounds of the underlying schemes, where the coefficients are small constants and the number $`q` of sessions started with its T oracle.

:::leanPill "partial"
:::

{usesLabel}`uses` {uses "aeneas_full_reduction"}[] · {uses "aeneas_full_assumptions"}[] · {uses "spec_uake_security"}[]
::::

:::defTitle "aeneas_full_security_dh" "Security of the high-fidelity extraction, non-PQ setting"
:::

::::theorem "aeneas_full_security_dh" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.uakeInitiator_secure_dh")
Top-level UAKE security theorem for the high-fidelity extraction, assuming the underlying DH key exchange is hard to break. This models UAKE security in the non-PQ setting: the adversary's advantage in the UAKE game is bounded as a polynomial over the adversary bounds of the underlying schemes, where the coefficients are small constants and the number $`q` of sessions started with its T oracle.

:::leanPill "partial"
:::

{usesLabel}`uses` {uses "aeneas_full_reduction"}[] · {uses "aeneas_full_assumptions"}[] · {uses "spec_uake_security"}[]
::::
