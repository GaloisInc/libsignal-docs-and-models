import VersoManual
import Book.Annotation
import Book.CodeRef
import Book.RustCode
import Book.Papers
import Book.PQXDH
import Book.SPQR
import Book.TripleRatchet

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Signal Protocols, Annotated" =>

%%%
authors := ["Galois, Inc."]
%%%

This document is an annotated port of two Signal protocol specifications,
plus an implementation-focused account of how they feed the ongoing Triple
Ratchet. All three are cross-referenced with their libsignal implementations:

* The PQXDH (Post-Quantum Extended Diffie-Hellman) key agreement protocol
  {citep Book.Papers.signalPQXDH}[].
* The ML-KEM Braid protocol, also known as SPQR
  {citep Book.Papers.signalMLKEMBraid}[].
* The Triple Ratchet construction that combines the Double Ratchet and SPQR
  {citep Book.Papers.signalSPQRBlog}[].

The upstream Signal specifications are the canonical references. This
document combines that spec text with Galois commentary mapping each
section to the libsignal Rust implementation.

{include 0 Book.PQXDH}

{include 0 Book.SPQR}

{include 0 Book.TripleRatchet}
