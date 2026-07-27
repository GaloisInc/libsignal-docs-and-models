import Verso
import VersoManual
import VersoBlueprint
import PQXDHDocs.Visuals.GameBoxes
import PQXDHDocs.Visuals.AnchorPill

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Message-Transmission Protocol Definitions" =>

:::group "mtp"
Interactive message-transmission games (iCCA, iCMA) and their theorems.
:::

The definitions and theorems below are documentation placeholders pending write-up, each marked $`\todo`; the Lean sources they will anchor to already live under the `PQXDH.MTP` namespace.

:::defTitle "mtp_party" "Message-transmission party and protocol"
:::

::::definition "mtp_party" (parent := "mtp")
$`\todo`

:::leanPill "planned"
:::
::::

:::defTitle "mtp_icca" "iCCA game (interactive message secrecy)"
:::

::::definition "mtp_icca" (parent := "mtp")
$`\todo`

:::leanPill "planned"
:::

{usesLabel}`uses` {uses "mtp_party"}[]
::::

:::defTitle "mtp_icma" "iCMA game (interactive message authentication)"
:::

::::definition "mtp_icma" (parent := "mtp")
$`\todo`

:::leanPill "planned"
:::

{usesLabel}`uses` {uses "mtp_party"}[]
::::

:::defTitle "mtp_theorems" "MTP security theorems"
:::

::::theorem "mtp_theorems" (parent := "mtp")
$`\todo`

:::leanPill "planned"
:::

{usesLabel}`uses` {uses "mtp_icca"}[] · {uses "mtp_icma"}[]
::::
