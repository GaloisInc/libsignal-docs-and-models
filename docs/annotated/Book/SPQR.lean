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

{include 1 Book.SPQR.CodeStructure}

{include 1 Book.SPQR.Protocol}

{include 1 Book.SPQR.Security}
