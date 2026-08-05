import Verso
import VersoManual
import VersoBlueprint
import PQXDHDocs.Visuals.GameBoxes
import PQXDHDocs.Visuals.AnchorPill
import PQXDH.Spec.UAKE.Defs
import PQXDH.Spec.UAKE.Correctness
import PQXDH.Spec.UAKE.Security
import ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman

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

#doc (Manual) "PQXDH Specification Definitions" =>

:::group "spec"
The PQXDH key-agreement protocol modeled as a DF'17-style unilaterally-authenticated key exchange (UAKE).
:::

Each atom below anchors to its Lean declaration under the `PQXDH` namespace; the accompanying prose is that declaration's docstring, rendered from the source at build time. Atoms still marked $`\todo` are awaiting a docstring on the Lean side.

:::defTitle "spec_parameters" "PQXDH protocol parameters"
:::

::::definition "spec_parameters" (parent := "spec") (lean := "PQXDH.Parameters")
$`\todo`
::::

:::defTitle "spec_protocol" "PQXDH protocol (spec model)"
:::

::::definition "spec_protocol" (parent := "spec") (lean := "PQXDH.initiate")
$`\todo`

{usesLabel}`uses` {uses "spec_parameters"}[]
::::

:::defTitle "spec_ddh" "Nominal-group DDH assumption"
:::

::::definition "spec_ddh" (parent := "spec") (lean := "PQXDH.DiffieHellman.nominalDDHDistAdvantage")
Nominal-group DDH assumptions.
::::

:::defTitle "spec_uake" "PQXDH as a UAKE"
:::

::::definition "spec_uake" (parent := "spec") (lean := "PQXDH.uakeInitiator")
$`\todo`

{usesLabel}`uses` {uses "spec_protocol"}[] · {uses "uake_scheme"}[]
::::

:::defTitle "spec_uake_recipient" "PQXDH recipient as a UAKE"
:::

::::definition "spec_uake_recipient" (parent := "spec") (lean := "PQXDH.uakeRecipient")
$`\todo`

{usesLabel}`uses` {uses "spec_protocol"}[] · {uses "uake_scheme"}[]
::::

:::defTitle "spec_uake_correctness" "Correctness of PQXDH"
:::

::::theorem "spec_uake_correctness" (parent := "spec") (lean := "PQXDH.uakeInitiator_perfectlyCorrect")
$`\todo`

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "uake_perfectly_correct"}[]
::::

:::defTitle "spec_uake_security" "UAKE security of PQXDH"
:::

::::theorem "spec_uake_security" (parent := "spec") (lean := "PQXDH.uakeInitiator_secure_pq")
$`\todo`

:::leanPill "partial"
:::

{usesLabel}`uses` {uses "spec_uake"}[] · {uses "spec_ddh"}[] · {uses "uake_exp"}[]
::::
