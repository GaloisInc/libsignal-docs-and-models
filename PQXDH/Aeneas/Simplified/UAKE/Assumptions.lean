/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import PQXDH.Aeneas.Simplified.UAKE.SecurityDefs

open OracleSpec OracleComp

namespace PQXDH.Aeneas.Simplified

/- True of the Rust, not provable here: the demo crate declares `mlkem_encapsulate` as a
`#[charon::opaque]` native with the infallible signature
`fn mlkem_encapsulate([u8; 1568], [u8; 32]) -> ([u8; 32], [u8; 1569])`, so encapsulation always
returns a value; the `Result` on the extracted axiom exists only because Aeneas conservatively
wraps every opaque call in `Result`. We cannot derive totality here because the axiom has no
body. -/
lemma encapsTotalAll : EncapsTotalAll := sorry

end PQXDH.Aeneas.Simplified
