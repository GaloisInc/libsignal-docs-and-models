import Verso
import VersoManual
import VersoBlueprint
import PQXDHDocs.Visuals.GameBoxes
import PQXDHDocs.Visuals.AnchorPill
import PQXDHDocs.Bibliography
import PQXDH.Spec.UAKE.Defs
import PQXDH.Spec.UAKE.Correctness
import PQXDH.Spec.UAKE.WellFormed
import PQXDH.Spec.UAKE.Security
import ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

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

#doc (Manual) "PQXDH Specification Definitions" =>

:::group "spec"
The PQXDH key-agreement protocol modeled as a DF'17-style unilaterally-authenticated key exchange (UAKE).
:::

This is a direct Lean implementation of PQXDH based on the [spec](https://signal.org/docs/specifications/pqxdh/pqxdh.pdf). Like that document, we use the convention that the initiator is Alice, and the recipient is Bob.

*Model simplifications*

- **Bob's extra message.** In the PQXDH spec, the exchange ends at Alice's first message to Bob, but UAKE requires that the last message be sent by the keyed party (Bob). Therefore we add an extra message from Bob under the AEAD at the end of the protocol in the T=Bob case. This would represent the second message in the conversation between Alice and Bob. We represent this by returning $`(sk, kb, ad, m)`, rather than just the shared key $`sk`, if Bob's `accept` procedure succeeds. Here, $`m` and $`ad` are the same as the message and additional data sent by Alice in her AEAD message, and $`kb` is an AEAD key, output by the KDF independently from the shared secret and Alice's AEAD key. This is then sent to Alice, who uses the `confirm` procedure to check that it decrypts under the same $`kb` and has the correct content, and returns $`sk`, if so. The T=Alice case is PQXDH as written in the spec.
- **No key reuse between DH and signatures.** We assume that Bob's identity key contains separate keys for DH exchange and signing. This matches the "no key reuse" simplification mentioned in Sec. 4 of the spec that other formal analyses required.
- **Separate AEAD key.** The PQXDH spec uses the same KDF output for both Alice's AEAD key and the final result of the key exchange, but this seems to preclude key indistinguishability. This is because the adversary can try using the candidate key to decrypt Alice's message. This will fail for a random key (with high likelihood) but succeed for the real key, thus distinguishing them. The spec allows $`K_A` to be $`SK` or $`PRF(SK, \cdot)`, but both variants break key indistinguishability. This could be easily fixed by using the KDF output as the key to a PRF that generates **both** $`SK` and $`K_A`, but the spec **only describes a PRF-derived** $`K_A`, which is insufficient. We sidestep this and model the final key and Alice's AEAD key (and Bob's AEAD key) as separate KDF outputs.

# Parameters and key material

:::defTitle "spec_parameters" "PQXDH protocol parameters"
:::

::::definition "spec_parameters" (parent := "spec") (lean := "PQXDH.Parameters, PQXDH.SignatureInput, PQXDH.EncodeEC, PQXDH.EncodeKEM, PQXDH.KeyMaterial")
Constants and primitive cryptographic operations used by PQXDH. Rather than instantiating the spec implementation with concrete cryptographic algorithms (the paper gives several alternatives), we use VCVio's existing abstract notions of a KEM scheme and a signature scheme. A relevant AEAD primitive does not appear in VCVio, so we use our own formalization, in the ToVCVio package for potential upstreaming.

- `gen`: generator for the Diffie-Hellman group.
- `pqkem`: KEM used for the post-quantum portion of the key exchange.
- `sig`: signature scheme used for signing keys. We need the same signature scheme to sign both DH and KEM public keys, so its input type is a sum of the two, with `EncodeEC` and `EncodeKEM` encoding each kind of key as a signature-scheme input.
- `aead`: AEAD used for the initial PQXDH message.
- `kdf`: key derivation function used to generate the session key that results from the exchange, as well as the AEAD keys, from the key material. We model this as an arbitrary function that might be instantiated by, e.g., a PRF or a RO.
- `idEC`, `idKEM`: functions that map DH and KEM public keys to key identifiers.
::::

:::defTitle "spec_keys" "Party key material"
:::

::::definition "spec_keys" (parent := "spec") (lean := "PQXDH.InitiatorParameters, PQXDH.RecipientIdentity, PQXDH.RecipientParameters")
The parameters given to Alice on startup: her long-term identity DH keypair; Bob's identity DH public key, included in order to pin Bob's identity to Alice, modeling the out-of-band key fingerprinting from Sec. 4.1 of the spec; Bob's signature-scheme public key; and the message Alice intends to send to Bob in the initial AEAD ciphertext.

*Deviation from spec:* we make a simplifying assumption that Bob's identity key contains independently chosen values for DH and signature scheme keys. This conflicts with the verbatim wording of the spec, but it is mentioned in Sec. 4 as a simplifying assumption used in previous analyses.

On Bob's side, his full set of long- and medium-term key pairs, including identity key, signing key, and signed (medium-term) pre-key; and the parameters given to him on startup, which additionally carry his one-time key pair (which may be empty) and his (short-term) KEM key pair.

{usesLabel}`uses` {uses "spec_parameters"}[]
::::

:::defTitle "spec_messages" "Protocol messages and session state"
:::

::::definition "spec_messages" (parent := "spec") (lean := "PQXDH.PreKeyBundle, PQXDH.InitialMessage, PQXDH.SessionContext")
The bundle of Bob's public key material fetched by Alice at the start of the protocol: his identity public key, the public halves of his signed DH pre-key and (optional) one-time DH pre-key, his post-quantum KEM public pre-key (each along with its key identifier), and his signatures for the SPK and PQ pre-key.

The initial message from Alice to Bob: her identity and ephemeral DH public keys, her KEM ciphertext, key identifiers for Bob's pre-keys, and the AEAD ciphertext of her initial message, encrypted using the derived shared key.

The session context stored by Alice after running `initiate` and sending her AEAD ciphertext, subsequently used by the `confirm` procedure: the shared key $`sk` output by the KDF, Bob's AEAD key $`kb`, and the additional data and message used in the AEAD ciphertexts.

*Deviation from spec:* in the PQXDH spec, Bob does not send an AEAD message, only Alice does. This extra AEAD ciphertext from Bob (which might represent the second message in the exchange, in the same way that Alice's AEAD ciphertext represents the first) is required in order to realize the T=Bob UAKE direction without being trivially insecure; `kb` is output by the KDF independently of `sk` for this purpose.

{usesLabel}`uses` {uses "spec_parameters"}[] · {uses "spec_keys"}[]
::::

# Protocol procedures

:::defTitle "spec_protocol" "PQXDH protocol (spec model)"
:::

::::definition "spec_protocol" (parent := "spec") (lean := "PQXDH.dhKeygen, PQXDH.DH, PQXDH.genOPK, PQXDH.setup, PQXDH.publish, PQXDH.initiate, PQXDH.accept, PQXDH.confirm")
The protocol procedures, traceable to the PQXDH spec.

- `dhKeygen`: generate a DH keypair $`(pk, sk) = (g^x, x)`, for a uniformly chosen exponent $`x`; `DH` generates a DH shared key $`g^{xy}`, given a secret key $`y` and a public key $`g^x`. `genOPK` generates a DH OPK only if `hasOPK` is true.
- `setup`: create the long-term state used by Alice and Bob respectively for all sessions.
- `publish`: compute Bob's key bundle to send to Alice. *Deviation from spec:* in the spec, this is retrieved by Alice from a third-party server; however, in UAKE we have only two parties, so we make this a message from Bob.
- `initiate`: compute Alice's initial message to Bob, including her public keys and the initial AEAD ciphertext. *Deviation from spec:* it seems necessary to assume that the keys used for the AEAD encrypted ciphertexts are independent of $`SK` and of each other; here, we make them distinct outputs of the KDF. Using $`SK` to key the AEAD and revealing the message appears to be incompatible with key indistinguishability, since an attacker can distinguish the key from random by using the candidate key to decrypt the initial message and checking whether it succeeds.
- `accept`: Bob's confirmation procedure. Check if Alice's AEAD ciphertext decrypts with the correct AD and KDF-derived key, and return $`sk` if so, along with the key, message, and AD for Bob's own AEAD ciphertext. *Deviation from spec:* Bob's AEAD ciphertext is not present in the spec, but it is needed in order to fit the UAKE security definition in the T=Bob case.
- `confirm`: Alice's confirmation procedure. Check if Bob's AEAD ciphertext decrypts with the correct message, AD, and KDF-derived key, and return the shared key, if so.

{usesLabel}`uses` {uses "spec_parameters"}[] · {uses "spec_keys"}[] · {uses "spec_messages"}[]
::::

# PQXDH as a UAKE

Using our Lean implementation of the PQXDH spec, we construct a unilaterally authenticated key exchange scheme, as described in {Informal.citet DF17}[]. The "unilateral" part of a UAKE means that its two parties play different roles: the T party is authenticated, and UAKE security ensures that the adversary cannot spoof its messages in an exchange; the U party is unauthenticated, and merely checks the T party's authenticity. For that reason, we instantiate the protocol twice, once with Alice as T, and once with Bob as T. These two instantiations need slightly different shapes, due to the convention from DF'17 that "T speaks last": in both cases the initial message is from Bob, so the T=Bob case is 3-round, with an extra confirmation message from Bob, whereas the T=Alice case is the standard 2-round protocol.

*Model simplifications*

- **Medium-term secrets as long-term.** The spec describes SPK and PQSPK as "changed periodically", but the UAKE security game only allows for permanent (via setup) and per-session (via init) keys. We model SPK (and its signature) as permanent, along with the identity keys.
- **No fallback KEM key.** We do not (currently) model the spec's last-resort KEM key (PQSPK); we generate a one-time KEM key every time, and plan to extend the model to include the fallback branch in the future. This is not necessarily a simple extension, since the fallback branch we omit is substantively weaker: according to Section 4.7 of the spec, compromising PQSPK in a PQ setting retroactively compromises the session's SK in the fallback case, and Sections 4.2 and 4.3 note that replay becomes possible if a one-time key is omitted.
- **Key bundle as a message from Bob.** The PQXDH spec describes the key bundle as coming from a third-party server. Since UAKE is a two-party protocol, we model it as coming from Bob instead.
- **KEM public key unconditionally included in AD.** The spec requires Bob's KEM public key to be included in AD "if pqkem does not incorporate \[it\] into the ciphertext." We unconditionally include it, which allows us to make no such assumption about the KEM.

:::defTitle "spec_uake" "PQXDH as a UAKE, Bob as T"
:::

::::definition "spec_uake" (parent := "spec") (lean := "PQXDH.uakeInitiator, PQXDH.initiator, PQXDH.recipient, PQXDH.Message")
UAKE scheme in which Bob plays the part of the authenticated party T and sends a final AEAD ciphertext to match the "T speaks last" convention from DF'17. Alice is the unkeyed party. Three messages are sent: Bob's pre-key bundle, then Alice's initiate message, then Bob's confirmation message.

Alice's Party state machine internally uses the `initiate` function, traceable to the PQXDH spec, followed by the `confirm` function, which checks Bob's AEAD ciphertext (not in the spec). Bob's Party state machine internally uses the `accept` and `publish` functions, traceable to the PQXDH spec, as well as sending a final AEAD message (not in the spec).

*Deviation from spec:* UAKE requires T to speak last, sending an authenticated message if the exchange was accepted. This prevents a trivial attack where the attacker simply refrains from sending Alice's last message, so that ping-pong is vacuously false. We have Bob send the final message of the exchange in order to satisfy this, whereas the spec stops at Bob receiving the message.

{usesLabel}`uses` {uses "spec_protocol"}[] · {uses "uake_scheme"}[]
::::

:::defTitle "spec_uake_recipient" "PQXDH as a UAKE, Alice as T"
:::

::::definition "spec_uake_recipient" (parent := "spec") (lean := "PQXDH.uakeRecipient, PQXDH.initiatorNoConfirm, PQXDH.recipientNoConfirm")
UAKE scheme in which Alice plays the part of the authenticated party T. Bob is the unkeyed party. Two messages are sent: Bob's pre-key bundle, then Alice's initiate message. This case is PQXDH as written in the spec: Alice's Party state machine internally uses the `initiate` function and Bob's internally uses the `publish` and `accept` functions, all traceable to the PQXDH spec.

{usesLabel}`uses` {uses "spec_protocol"}[] · {uses "uake_scheme"}[]
::::

# Correctness

:::defTitle "spec_uake_correctness" "Correctness of PQXDH, Bob as T"
:::

::::theorem "spec_uake_correctness" (parent := "spec") (lean := "PQXDH.uakeInitiator_perfectlyCorrect")
Spec-based PQXDH in the T=Bob direction has perfect UAKE correctness, assuming the KEM and AEAD are perfectly correct and the signature is perfectly complete (i.e., never fails on an honestly generated signature, when paired with the message used to generate it).

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_perfectly_correct"}[]
::::

:::defTitle "spec_uake_recipient_correctness" "Correctness of PQXDH, Alice as T"
:::

::::theorem "spec_uake_recipient_correctness" (parent := "spec") (lean := "PQXDH.uakeRecipient_perfectlyCorrect")
Spec-based PQXDH in the T=Alice direction has perfect UAKE correctness, assuming the KEM and AEAD are perfectly correct and the signature is perfectly complete (i.e., never fails on an honestly generated signature, when paired with the message used to generate it).

{usesLabel}`uses` {uses "spec_uake_recipient"}[] · {uses "uake_perfectly_correct"}[]
::::

# Well-formedness

:::defTitle "spec_uake_wellformed" "Well-formedness of PQXDH as a UAKE"
:::

::::theorem "spec_uake_wellformed" (parent := "spec") (lean := "PQXDH.uakeInitiator_wellFormed, PQXDH.uakeRecipient_wellFormed")
Both orientations of the Spec-model scheme are well-formed, assuming the KEM and AEAD are perfectly correct and the signature is perfectly complete: each party produces output exactly when its protocol run completes, and an honest run transfers exactly `rounds` messages (3 in the T=Bob direction, 2 in the T=Alice direction).

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "spec_uake_recipient"}[] · {uses "uake_scheme_wellformed"}[]
::::

# Security

We model UAKE security of the spec by bounding the adversary's advantage in the UAKE game based on its advantage in the security games of the underlying cryptographic primitives.

*Model simplifications*

- **Unilateral authentication.** UAKE is unilaterally authenticated. In principle, it should be possible to model a protocol in both directions to show multilateral authentication. However, we model security only for the "Bob authenticates to Alice" direction. This is because UAKE security requires explicit authentication, and Alice's authentication to Bob is implicit via the adversary being unable to compute the DH output, rather than relying on Alice's signature (she signs nothing).
- **SUF-CMA signature (not EUF-CMA).** Since UAKE is a transcript-matching-style definition, our security theorems are subject to harmless but definition-breaking "no-match" attacks on the signature scheme. See Li & Schäge, "No-Match Attacks and Robust Partnering Definitions" (ACM CCS 2017) for a reference on attacks of this kind.
- **PQ-secure signature scheme.** In order to re-use our AKE definition in the post-quantum case, we assume that the signature scheme is *still secure*, even in the post-quantum setting. In reality, PQXDH uses an EC-based signature scheme, which is insecure against a quantum adversary. This is not a problem for the protocol, since the desired PQ security is security against HNDL attacks, which requires only secrecy, not integrity. However, UAKE cannot capture secrecy alone. A better way to model this kind of security would be to use a secrecy-only definition.
- **Injective key→ID maps.** We assume that the function mapping KEM keys to identifiers is injective. Section 4.13 of the spec contains the weaker requirement that "collisions are unlikely". Modeling the maps as collision resistant would be an improvement, since it would allow a hash of the key to be used, but we leave that as a future improvement.

:::defTitle "spec_security_defs" "KDF models and adversary query bound"
:::

::::definition "spec_security_defs" (parent := "spec") (lean := "PQXDH.kdfPRF, PQXDH.kdfPRFDH, AKE.UAKE.Adversary.OpensAtMost")
The KDF modeled as a PRF, keyed either by a bitstring (e.g., the output of the KEM) or by a DH group element (e.g., the output of a DH key exchange), and the predicate bounding the number of sessions started by the adversary with its T oracle, by bounding the number of `openT` queries.

{usesLabel}`uses` {uses "spec_parameters"}[] · {uses "uake_adversary"}[]
::::

:::defTitle "spec_ddh" "GapDH assumption"
:::

::::definition "spec_ddh" (parent := "spec") (lean := "PQXDH.DiffieHellman.gapDHAdvantage")
The GapDH security game and advantage. The non-PQ security theorem assumes a bound on an adversary's advantage in this game.
::::

:::defTitle "spec_uake_security_dh" "UAKE security of PQXDH, non-PQ setting"
:::

::::theorem "spec_uake_security_dh" (parent := "spec") (lean := "PQXDH.uakeInitiator_secure_dh")
Top-level UAKE security theorem for spec-based PQXDH, assuming the underlying DH key exchange is hard to break. This models UAKE security in the non-PQ setting: the adversary's advantage in the UAKE game is bounded as a polynomial over the adversary bounds of the underlying schemes, where the coefficients are small constants and the number $`q` of sessions started with its T oracle.

For any UAKE adversary who starts at most $`q` sessions with its T oracle, we assume: the function mapping KEM keys to key identifiers is injective; a bound $`\varepsilon_{\mathrm{sig}}` on an adversary's advantage in forging a signature; a bound $`\varepsilon_{\mathrm{gap}}` on an adversary's advantage in the DH security game; a bound $`\varepsilon_{\mathrm{aead}}` on the adversary's advantage forging an AEAD ciphertext; and a bound $`\varepsilon_{\mathrm{kdf}}` on an adversary's distinguishing advantage for the KDF, modeled as a PRF. Since we key the KDF using DH group elements, we must also assume that the KDF is secure when keyed with one of these, rather than a random bit string. We also assume a bound $`\varepsilon_{\mathrm{pk}}` on the probability of guessing the public key output by the KEM's key generation; this bounds KEM public-key collisions and predictions across T-oracle sessions, which otherwise seem to break UAKE security.

We additionally assume the signature scheme has a deterministic verification procedure. This holds in general for signature schemes, but VCV-io's signature scheme definition leaves it monadic, so this seems to be a modeling gap.

:::leanPill "partial"
:::

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "spec_ddh"}[] · {uses "spec_security_defs"}[] · {uses "uake_exp"}[] · {uses "spec_lemma_advantage_le_forgeProb_add_indistAdvantage"}[] · {uses "spec_lemma_forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood"}[] · {uses "spec_lemma_sigForgeProb_le_sig"}[] · {uses "spec_lemma_pqpkGuessedProb_le"}[] · {uses "spec_lemma_forgeHonestGoodProb_le_gap"}[] · {uses "spec_lemma_indistAdvantage_le_gap"}[]
::::

:::defTitle "spec_uake_security" "UAKE security of PQXDH, PQ setting"
:::

::::theorem "spec_uake_security" (parent := "spec") (lean := "PQXDH.uakeInitiator_secure_pq")
Top-level UAKE security theorem for spec-based PQXDH, making no assumptions about the underlying DH key exchange, but assuming the KEM is secure. This models UAKE security in the PQ setting: the adversary's advantage in the UAKE game is bounded as a polynomial over the adversary bounds of the underlying schemes, where the coefficients are small constants and the number $`q` of sessions started with its T oracle.

For any UAKE adversary who starts at most $`q` sessions with its T oracle, we assume: the function mapping KEM keys to key identifiers is injective; the KEM is perfectly correct; a bound $`\varepsilon_{\mathrm{sig}}` on an adversary's advantage in forging a signature; a bound $`\varepsilon_{\mathrm{kem}}` on an adversary's advantage in the IND-CCA game for the KEM; a bound $`\varepsilon_{\mathrm{aead}}` on the adversary's advantage forging an AEAD ciphertext; and a bound $`\varepsilon_{\mathrm{kdf}}` on an adversary's distinguishing advantage for the KDF, modeled as a PRF keyed by the KEM secret. We also assume a bound $`\varepsilon_{\mathrm{pk}}` on the probability of guessing the public key output by the KEM's key generation; this bounds KEM public-key collisions and predictions across T-oracle sessions, which otherwise seem to break UAKE security.

We additionally assume the signature scheme has a deterministic verification procedure. This holds in general for signature schemes, but VCV-io's signature scheme definition leaves it monadic, so this seems to be a modeling gap.

:::leanPill "partial"
:::

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "spec_security_defs"}[] · {uses "uake_exp"}[] · {uses "spec_lemma_advantage_le_forgeProb_add_indistAdvantage"}[] · {uses "spec_lemma_forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood"}[] · {uses "spec_lemma_sigForgeProb_le_sig"}[] · {uses "spec_lemma_pqpkGuessedProb_le"}[] · {uses "spec_lemma_forgeHonestGoodProb_le_pq"}[] · {uses "spec_lemma_indistAdvantage_le_pq"}[]
::::
