import Verso
import VersoManual
import VersoBlueprint
import PQXDHDocs.Visuals.GameBoxes
import PQXDHDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "PQXDH Specification Definitions" =>

:::group "spec"
The PQXDH key-agreement protocol modeled as a DF'17-style unilaterally-authenticated key exchange (UAKE).
:::

The definitions and theorems below are documentation placeholders pending write-up, each marked $`\todo`; the Lean sources they will anchor to already live under the `PQXDH.Spec` and `PQXDH.HardnessAssumptions` namespaces.

:::defTitle "spec_parameters" "PQXDH protocol parameters"
:::

::::definition "spec_parameters" (parent := "spec")
$`\todo`

:::leanPill "planned"
:::
::::

:::defTitle "spec_protocol" "PQXDH protocol (spec model)"
:::

::::definition "spec_protocol" (parent := "spec")
$`\todo`

:::leanPill "planned"
:::

{usesLabel}`uses` {uses "spec_parameters"}[]
::::

:::defTitle "spec_ddh" "Nominal-group DDH assumption"
:::

::::definition "spec_ddh" (parent := "spec")
Nominal-group DDH assumptions.

:::leanPill "planned"
:::
::::

:::defTitle "spec_uake" "PQXDH as a UAKE"
:::

::::definition "spec_uake" (parent := "spec")
$`\todo`

:::leanPill "planned"
:::

{usesLabel}`uses` {uses "spec_protocol"}[]
::::

:::defTitle "spec_uake_security" "UAKE security of PQXDH"
:::

::::theorem "spec_uake_security" (parent := "spec")
$`\todo`

:::leanPill "planned"
:::

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "spec_ddh"}[]
::::
