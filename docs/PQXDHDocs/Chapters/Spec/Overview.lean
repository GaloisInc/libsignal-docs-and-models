import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import PQXDHDocs.Bibliography
import PQXDHDocs.Chapters.Spec.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "PQXDH Protocol Specification" =>

*References:*

- {Informal.citet PQXDHSpec}[]
- {Informal.citet DF17}[]
- {Informal.citet LS17}[]

PQXDH is modeled as a DF'17-style UAKE. The following modeling notes are drawn
from the specification sources.

*Model simplifications*

*Unilateral authentication:* UAKE is unilaterally authenticated. In
principle, it should be possible to model a protocol in both directions to
show multilateral authentication. However, we model security only for the
"Bob authenticates to Alice" direction. This is because UAKE security
requires explicit authentication, and Alice's authentication to Bob is
implicit via the adversary being unable to compute the DH output, rather than
relying on Alice's signature (she signs nothing).

*SUF-CMA signature (not EUF-CMA):* Since UAKE is a
transcript-matching-style definition, our security theorems are subject to
harmless but definition-breaking "no-match" attacks on the signature scheme.
See Li & Schäge, "No-Match Attacks and Robust Partnering Definitions" (ACM CCS
2017) for a reference on attacks of this kind.

*Bob's extra message:* In the PQXDH spec, the exchange ends at Alice's
first message to Bob, but UAKE requires that the last message be sent by the
keyed party (Bob). Therefore we add an extra message from Bob under the AEAD
at the end of the protocol. This would represent the second message in the
conversation between Alice and Bob.

*Medium-term secrets as long-term:* The spec describes SPK and PQSPK as
"changed periodically", but the UAKE security game only allows for permanent
(via setup) and per-session (via init) keys. We model SPK (and its signature)
as permanent, along with IK_A / IK_B.

*No fallback KEM key:* We do not (currently) model the spec's last-resort
KEM key (PQSPK). We generate a one-time KEM key (PQOPKᵢ) every time. This is
a pure simplification, and we plan to extend the model to include the
last-resort KEM key in the future.

*Protocol questions*

*Key reuse between DH and SignatureAlg:* We assume that Bob's identity key
contains separate keys for DH exchange and signing. This matches the "no key
reuse" simplification mentioned in Sec. 4 of the spec that other formal
analyses required.

*Separate AEAD key:* The PQXDH spec uses the same KDF output for both
Alice's AEAD key and the final result of the key exchange, but this seems to
preclude key indistinguishability. This is because the adversary can try
using the candidate key to decrypt Alice's message. This will fail for a
random key (with high likelihood) but succeed for the real key, thus
distinguishing them. The spec allows KA to be SK or PRF(SK, ·), but both
variants break key indistinguishability. This could be easily fixed by using
the KDF output as the key to a PRF that generates *both* SK and KA, but
the spec *only describes a PRF-derived KA*, which is insufficient. We
sidestep this and model the final key and Alice's AEAD (and Bob's AEAD key;
see bullet 3 of "Model simplifications") as separate KDF outputs.

{include 1 PQXDHDocs.Chapters.Spec.Defs}

{blueprint_graph}

{blueprint_summary}
