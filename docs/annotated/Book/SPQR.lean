import VersoManual
import Book.Annotation
import Book.SPQR.CodeStructure
import Book.SPQR.Protocol
import Book.SPQR.Security

open Verso.Genre Manual

#doc (Manual) "SPQR — Docs to Code" =>

:::galois
The following document is an annotated version of Signal's documentation of the ML-KEM Braid Protocol \[[1](https://signal.org/docs/specifications/mlkembraid/)\] with the associated code found in \[[2](https://github.com/signalapp/SparsePostQuantumRatchet)\] specifically at commit \[[49d300b](https://github.com/signalapp/libsignal/commit/49d300ba667501467409bacd9a02395a7a5a62a7)\]. As a result, the text combines text from both sources and we highlight in pink any new addition. This document's structure follows the same structure as the one in the Signal docs for ease of following along with the original documentation. We omit several sections of the signal docs, any pseudo code and several diagrams in order to avoid cluttering this document. We also omit certain pieces of the code that may not be useful for following along.
:::

:::claude
*Audit against upstream Signal ML-KEM Braid spec* (`signal.org/docs/specifications/mlkembraid/`, Revision 1, 2025-02-21).

Sections present here match upstream prose closely. The Galois port is significantly more lossy relative to upstream than the PQXDH port — substantial portions are omitted by design.

*Deliberate omissions* (per the Galois intro):

- All of Chapter 1 (Introduction) — sections 1.1 (Sparse Continuous Key Agreement), 1.2 (Incremental KEMs), 1.2.1 (ML-KEM as an Incremental KEM), 1.3 (Chunking with Erasure Codes).
- Section 2.6 (Initialization).
- All pseudocode in section 2.5 state-transition descriptions (the `def State.Send(...)` and `def State.Receive(...)` definitions); only the Rust excerpts from libsignal are kept.
- Most of chapter 3 — sections 3.2 (Alternate KEMs), 3.3 (Optional internal authentication), 3.4 (Bandwidth limits), 3.6 (Alternate encoders), 3.7 (Formal verification and security proofs).
- The state-machine diagram figure ("Figure 1").

*Inserted Galois content* (not in upstream Signal spec):

- "Note on libsignal's code structure" — the entire opening chapter is Galois-authored commentary on the SparsePostQuantumRatchet repo layout.
- "Important Note on Post-Compromise Security" inside Security Considerations.

Galois copy-artifact corrections (silent restores) — `CHANGES.md` at the repo root logs each one for backport. Also: *_GF(216)_* appearing throughout is a PDF→text artifact from the upstream rendering of `GF(2^16)`; the Galois source preserved the broken form. The `KEM` bullet in §2.2 drops the final upstream sentence "The KEM exposes the incremental interface described in Section 1.2" — kept as Galois omitted it, since §1.2 itself is also omitted and the cross-reference would dangle.

No semantic divergence from upstream in the ported Signal prose.
:::

{include 1 Book.SPQR.CodeStructure}

{include 1 Book.SPQR.Protocol}

{include 1 Book.SPQR.Security}
