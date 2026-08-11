import VersoManual
import Book.Annotation
import Book.PQXDH.Preliminaries
import Book.PQXDH.Protocol
import Book.PQXDH.Todo

open Verso.Genre Manual

#doc (Manual) "PQXDH — Docs to Code" =>

:::galois
The following document is an annotated version of Signal's documentation of the ML-KEM Braid Protocol \[[1](https://signal.org/docs/specifications/pqxdh/)\] with the associated code found in \[[2](https://github.com/signalapp/libsignal)\] specifically at commit \[[7c8cb0c](https://github.com/signalapp/libsignal/tree/7c8cb0c5fce1d01805199de992bf4323f4765f1f)\]. As a result, the text combines text from both sources and we highlight in pink any new addition. This document's structure follows the same structure as the one in the Signal docs for ease of following along with the original documentation. We omit several sections of the signal docs, any pseudo code and several diagrams in order to avoid cluttering this document. We also omit certain pieces of the code that may not be useful for following along.

To make following this document easier, we have created a simple test example \[[see](https://github.com/GaloisInc/libsignal-testing/blob/tests/rust/protocol/tests/pqxdh.rs)\] of PQXDH embedded into a fork of libsignal at the mentioned commit (tests/[pqxdh.rs](https://github.com/GaloisInc/libsignal-testing/blob/tests/rust/protocol/tests/pqxdh.rs) is currently the only new file in that fork!). This example is a simplified version of another libsignal test \[[see](https://github.com/signalapp/libsignal/blob/main/rust/protocol/tests/session.rs)\]. This example models the initial handshake between Alice and Bob and only includes the very first message sent from Bob to Alice prior to the full ratcheting protocol. Additionally, this test creates a single pre-key bundle instead of multiple of them. The latter case follows the same logic as the former. We highly recommend running this test example with your favorite debugger and follow the stack trace of function calls and see exactly how libsignal realizes PQXDH.
:::

:::claude
The source describes this as an annotated version of "Signal's documentation of the ML-KEM Braid Protocol", but the linked Signal spec is `signal.org/docs/specifications/pqxdh/` and every subsequent section describes PQXDH. This is almost certainly a copy-paste typo carried over from the SPQR (ML-KEM Braid) sibling document — the protocol being annotated here is the PQXDH Key Agreement Protocol.
:::

:::claude
*Audit against upstream Signal PQXDH spec* (`signal.org/docs/specifications/pqxdh/`, Revision 3, 2023-05-24).

Sections present here match upstream prose closely. Deliberate omissions per the Galois intro: section 2.2 (Cryptographic notation), 2.3 (Roles), and the entire section 4 (Security considerations 4.1–4.13) are not ported.

Galois copy-artifact corrections (silent restores) and structural reshapings — `CHANGES.md` at the repo root logs each one for backport to the source markdown. No semantic divergence from upstream in the ported Signal prose.
:::

{include 1 Book.PQXDH.Preliminaries}

{include 1 Book.PQXDH.Protocol}

{include 1 Book.PQXDH.Todo}
