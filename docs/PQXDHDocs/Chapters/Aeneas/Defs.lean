import Verso
import VersoManual
import VersoBlueprint
import PQXDHDocs.Visuals.GameBoxes
import PQXDHDocs.Visuals.AnchorPill
import PQXDH.Aeneas.Simplified.UAKE
import PQXDH.Aeneas.Full.UAKE

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true
set_option doc.verso true

#doc (Manual) "Aeneas-Extracted PQXDH Definitions" =>

:::group "aeneas"
The Aeneas-extracted PQXDH realization and its reduction to the spec model.
:::

The descriptions below are documentation placeholders pending write-up, each marked $`\todo`. Two independent Aeneas extractions of PQXDH are modelled. The *simplified* extraction lives under the `PQXDH.Aeneas.Simplified` namespace and exposes each cryptographic step as a standalone Rust function. The *full* extraction lives under `PQXDH.Aeneas.Full` and is generated from Signal's production `libsignal_protocol` crate.

:::defTitle "aeneas_simplified_model" "Simplified extraction as a UAKE"
:::

::::definition "aeneas_simplified_model" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.uakeInitiator")
$`\todo`

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "aeneas_simplified_correctness" "Correctness of the simplified extraction"
:::

::::theorem "aeneas_simplified_correctness" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.uakeInitiator_perfectlyCorrect")
$`\todo`

{usesLabel}`uses` {uses "aeneas_simplified_model"}[]
::::

:::defTitle "aeneas_simplified_security" "Security of the simplified extraction"
:::

::::theorem "aeneas_simplified_security" (parent := "aeneas") (lean := "PQXDH.Aeneas.Simplified.uakeInitiator_secure_pq")
$`\todo`

{usesLabel}`uses` {uses "aeneas_simplified_model"}[] · {uses "spec_uake_security"}[]
::::

:::defTitle "aeneas_full_model" "Production extraction as a UAKE"
:::

::::definition "aeneas_full_model" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.uakeInitiator")
$`\todo`

{usesLabel}`uses` {uses "spec_uake"}[]
::::

:::defTitle "aeneas_full_assumptions" "Assumptions about the production extraction"
:::

::::definition "aeneas_full_assumptions" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.encaps_toKey_isSome")
$`\todo`

:::leanPill "partial"
:::
::::

:::defTitle "aeneas_full_correctness" "Correctness of the production extraction"
:::

::::theorem "aeneas_full_correctness" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.uakeInitiator_perfectlyCorrect")
$`\todo`

{usesLabel}`uses` {uses "aeneas_full_model"}[] · {uses "aeneas_full_assumptions"}[]
::::

:::defTitle "aeneas_full_reduction" "Reduction of the production extraction to the spec"
:::

::::theorem "aeneas_full_reduction" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.advantage_toSpec")
$`\todo`

{usesLabel}`uses` {uses "aeneas_full_model"}[] · {uses "spec_uake"}[]
::::

:::defTitle "aeneas_full_security" "Security of the production extraction"
:::

::::theorem "aeneas_full_security" (parent := "aeneas") (lean := "PQXDH.Aeneas.Full.uakeInitiator_secure_pq")
$`\todo`

:::leanPill "partial"
:::

{usesLabel}`uses` {uses "aeneas_full_reduction"}[] · {uses "spec_uake_security"}[]
::::
