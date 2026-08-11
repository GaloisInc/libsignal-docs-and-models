/-
Bibliographic entries for upstream references.

`Article` is the closest fit Verso ships for vendor-published technical
specifications; we treat the publication venue as "Signal Documentation"
and store the spec URL.
-/

import VersoManual

open Verso.Genre.Manual

namespace Book.Papers

def signalPQXDH : Article where
  title := inlines!"The PQXDH Key Agreement Protocol"
  authors := #[inlines!"Ehren Kret", inlines!"Rolfe Schmidt"]
  journal := inlines!"Signal Documentation"
  year := 2023
  month := none
  volume := inlines!"Revision 3"
  number := inlines!""
  pages := none
  url := some "https://signal.org/docs/specifications/pqxdh/"

def signalMLKEMBraid : Article where
  title := inlines!"The ML-KEM Braid Protocol"
  authors := #[inlines!"Rolfe Schmidt"]
  journal := inlines!"Signal Documentation"
  year := 2025
  month := none
  volume := inlines!"Revision 1"
  number := inlines!""
  pages := none
  url := some "https://signal.org/docs/specifications/mlkembraid/"

def signalSPQRBlog : InProceedings where
  title := inlines!"Signal Protocol and Post-Quantum Ratchets"
  authors := #[inlines!"Graeme Connell", inlines!"Rolfe Schmidt"]
  year := 2025
  booktitle := inlines!"Signal Blog"
  editors := none
  series := none
  url := some "https://signal.org/blog/spqr/"

def compareSecureMessaging : InProceedings where
  title := inlines!"How to Compare Bandwidth Constrained Two-Party Secure Messaging Protocols: A Quest for A More Efficient and Secure Post-Quantum Protocol"
  authors := #[
    inlines!"Benedikt Auerbach",
    inlines!"Yevgeniy Dodis",
    inlines!"Daniel Jost",
    inlines!"Shuichi Katsumata",
    inlines!"Rolfe Schmidt"
  ]
  year := 2025
  booktitle := inlines!"Proceedings of the 34th USENIX Security Symposium"
  editors := none
  series := none
  url := some "https://www.usenix.org/conference/usenixsecurity25/presentation/auerbach"

end Book.Papers
