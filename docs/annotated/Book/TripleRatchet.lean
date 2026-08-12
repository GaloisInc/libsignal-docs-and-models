import VersoManual
import Book.Annotation
import Book.TripleRatchet.Overview
import Book.TripleRatchet.Protocol
import Book.TripleRatchet.Keys
import Book.TripleRatchet.Security

open Verso.Genre Manual

#doc (Manual) "Triple Ratchet — Description & Code" =>

:::galois
The code described in this document is pinned to commit
\[[57d41c8](https://github.com/signalapp/libsignal/tree/57d41c877d5a55d881fb3f52d9b16900118ee29b)\]
of libsignal and
\[[f2589fe](https://github.com/signalapp/SparsePostQuantumRatchet/tree/f2589fef855c10f39d72634dab3d14654dd410bf)\]
of the SparsePostQuantumRatchet library. There is currently no documentation
that explicitly focuses on the Triple Ratchet protocol, i.e. the connection
between the Double Ratchet and SPQR. The docs on the Signal website instead
allude to how these parts interact. For that reason, we focus our work here on
describing how libsignal combines these parts, with references to the code, and
do our best to highlight instances of the Signal docs and Signal-related papers
that describe them.
:::
{include 1 Book.TripleRatchet.Overview}

{include 1 Book.TripleRatchet.Protocol}

{include 1 Book.TripleRatchet.Keys}

{include 1 Book.TripleRatchet.Security}

