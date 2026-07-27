import Verso
import VersoManual
import VersoBlueprint
import PQXDHDocs.Visuals.GameBoxes
import PQXDHDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Aeneas-Extracted PQXDH Definitions" =>

:::group "aeneas"
The Aeneas-extracted PQXDH realization and its reduction to the spec model.
:::

The definitions and theorems below are documentation placeholders pending write-up, each marked $`\todo`; the Lean sources they will anchor to already live under the `PQXDH.Aeneas` namespace.

:::defTitle "aeneas_extracted" "Aeneas-extracted PQXDH implementation"
:::

::::definition "aeneas_extracted" (parent := "aeneas")
$`\todo`

:::leanPill "planned"
:::
::::

:::defTitle "aeneas_uake" "Extracted PQXDH as a UAKE"
:::

::::definition "aeneas_uake" (parent := "aeneas")
$`\todo`

:::leanPill "planned"
:::

{usesLabel}`uses` {uses "aeneas_extracted"}[] · {uses "spec_uake"}[]
::::

:::defTitle "aeneas_reduction" "Reduction of extracted PQXDH to the spec"
:::

::::theorem "aeneas_reduction" (parent := "aeneas")
$`\todo`

:::leanPill "planned"
:::

{usesLabel}`uses` {uses "aeneas_uake"}[] · {uses "spec_uake_security"}[]
::::
