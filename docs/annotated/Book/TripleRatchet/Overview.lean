import VersoManual
import Book.Annotation
import Book.CodeRef
import Book.Figure
import Book.Papers

open Verso.Genre Manual

#doc (Manual) "High Level Description" =>

:::galois
The Signal protocol answers the following question at any point during
messaging:

> "What encryption key should I use for the next message?"

{citep Book.Papers.signalSPQRBlog}[]

That includes when:

1. *\[PQXDH\]* a session is first established between two interlocutors who
   have never spoken to one another before;
2. *\[Triple Ratchet: SPQR/ML-KEM Braid + Double Ratchet\]* an ongoing session
   is in progress between two people.

Because the Signal protocol involves two or more users continuously agreeing
on the keys they should use to encrypt their messages, it makes sense to think
of the Signal protocol in terms of a state machine that: (1) transitions
between states whenever a message is received and (2) determines what keys and
headers should be used for the next message.

Additionally, because the post-quantum (PQ) variant of Signal now involves a
sparse continuous key agreement protocol (SPQR/ML-KEM Braid) that gets mixed
into the user's encryption key material after a certain period of time, this state machine also tracks and
dictates when a new _epoch_ begins, where an epoch is associated with each SPQR
shared secret, and how the next SPQR shared secret is constructed between epochs.

In what follows, we focus on the transition of this state machine between the
different sub-protocols of the overall Signal protocol: i.e. PQXDH, Double
Ratchet, and SPQR/ML-KEM Braid.
:::

:::figure
![Triple Ratchet](static/triple-ratchet.png)

Diagram showing the interaction between PQXDH, the Triple Ratchet protocol and
the various components of the Triple Ratchet. What we call "Vulnerable Message
Key" in this figure, refers to the message keys associated with the vulnerable
set in the ML-KEM Braid specs. These are only vulnerable against a quantum
adversary, and are safe against a regular one.
:::

# {galois}[PQXDH → Triple Ratchet]

:::galois
The Signal docs describe the transition from the initial handshake (PQXDH) to
the ratcheting stage (SPQR/ML-KEM Braid + Double Ratchet); see sections 3.3,
3.4, and 4 of the PQXDH specification {citep Book.Papers.signalPQXDH}[].

At the beginning of time, Alice wants to communicate with Bob for the very
first time but does not have any shared secret with him. This lack of a shared
secret, and really a first key to ratchet from, defines this very first state.
In order to agree on the first key that will be in the
Double Ratchet chain, as well as the secret material for SPQR, Alice fetches
one of Bob's pre-key bundles from the Signal server and performs the initial
handshake (PQXDH) with him. By doing so, Alice
{libsignal57d "rust/protocol/src/ratchet.rs#L44-L107"}[] and Bob
{libsignal57d "rust/protocol/src/ratchet.rs#L118-L169"}[] know which keys to
use for their first messages.

Note that this initial ratcheting state includes both the first Double Ratchet
key and state, as well as the secret material necessary to initialize the SPQR
chain in the code base
{libsignal57d "rust/protocol/src/ratchet.rs#L48-L64"}[],
{libsignal57d "rust/protocol/src/ratchet.rs#L77-L107"}[]
{spqrf258 "src/lib.rs#L210-L234"}[]. Alice's initial SPQR state, described in
detail in the ML-KEM Braid specification
{citep Book.Papers.signalMLKEMBraid}[], is set to `KeysUnsampled`
{spqrf258 "src/lib.rs#L196-L202"}[],
{spqrf258 "src/v1/chunked/states.rs#L57-L60"}[], while Bob's is set to
`NoHeaderReceived`
{spqrf258 "src/lib.rs#L203-L205"}[],
{spqrf258 "src/v1/chunked/states.rs#L62-L64"}[].
:::
