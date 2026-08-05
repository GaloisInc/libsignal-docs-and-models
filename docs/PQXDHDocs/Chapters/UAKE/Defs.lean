import Verso
import VersoManual
import VersoBlueprint
import PQXDHDocs.Visuals.GameBoxes
import PQXDHDocs.Visuals.AnchorPill
import ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import ToVCVio.CryptoFoundations.AKE.UAKE.Party
import ToVCVio.CryptoFoundations.AKE.UAKE.Transcript

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.style.setOption false
set_option linter.hashCommand false
set_option linter.style.emptyLine false
set_option linter.style.longLine false
set_option linter.style.whitespace false
set_option verso.docstring.allowMissing true
set_option verso.blueprint.autoDeps true
set_option doc.verso true

#doc (Manual) "UAKE Model Definitions" =>

:::group "uake"
The unilaterally-authenticated key exchange (UAKE) model of {Informal.citet DF17}[], against which the PQXDH realizations are stated and proved.
:::

The prose on each atom below is the Lean docstring of the declaration it anchors to, rendered from the source at build time rather than restated here. The dependency edges are likewise derived from the Lean declarations, so no `uses` edge is recorded by hand in this chapter.

# Parties

:::defTitle "uake_party_init" "Party initialization result"
:::

::::definition "uake_party_init" (parent := "uake") (lean := "AKE.UAKE.Party.InitResult")
$`\todo`
::::

:::defTitle "uake_party_step" "Party step result"
:::

::::definition "uake_party_step" (parent := "uake") (lean := "AKE.UAKE.Party.StepResult")
$`\todo`
::::

:::defTitle "uake_party" "Party"
:::

::::definition "uake_party" (parent := "uake") (lean := "AKE.UAKE.Party")
$`\todo`
::::

:::defTitle "uake_party_outputs" "Outputs only at completion"
:::

::::definition "uake_party_outputs" (parent := "uake") (lean := "AKE.UAKE.Party.OutputsOnlyAtCompletion")
$`\todo`
::::

:::defTitle "uake_run_honest" "Honest protocol run"
:::

::::definition "uake_run_honest" (parent := "uake") (lean := "AKE.UAKE.Party.runHonest")
$`\todo`
::::

# Schemes and correctness

:::defTitle "uake_scheme" "UAKE scheme"
:::

::::definition "uake_scheme" (parent := "uake") (lean := "AKE.UAKE.Scheme")
$`\todo`
::::

:::defTitle "uake_scheme_wellformed" "Well-formed scheme"
:::

::::definition "uake_scheme_wellformed" (parent := "uake") (lean := "AKE.UAKE.Scheme.WellFormed")
$`\todo`
::::

:::defTitle "uake_correct_exp" "Correctness experiment"
:::

::::definition "uake_correct_exp" (parent := "uake") (lean := "AKE.UAKE.CorrectExp")
$`\todo`
::::

:::defTitle "uake_perfectly_correct" "Perfect correctness"
:::

::::definition "uake_perfectly_correct" (parent := "uake") (lean := "AKE.UAKE.PerfectlyCorrect")
$`\todo`
::::

# Transcripts

:::defTitle "uake_transcript" "Session transcript"
:::

::::definition "uake_transcript" (parent := "uake") (lean := "AKE.UAKE.Transcript")
$`\todo`
::::

:::defTitle "uake_matching" "Matching sessions"
:::

::::definition "uake_matching" (parent := "uake") (lean := "AKE.UAKE.Matching")
$`\todo`
::::

# The security experiment

:::defTitle "uake_tsession" "T-session state"
:::

::::definition "uake_tsession" (parent := "uake") (lean := "AKE.UAKE.TSession")
$`\todo`
::::

:::defTitle "uake_env" "Experiment environment"
:::

::::definition "uake_env" (parent := "uake") (lean := "AKE.UAKE.Env")
$`\todo`
::::

:::defTitle "uake_op" "Adversary oracle operations"
:::

::::definition "uake_op" (parent := "uake") (lean := "AKE.UAKE.Op")
$`\todo`
::::

:::defTitle "uake_op_impl" "T-session and challenge oracles"
:::

::::definition "uake_op_impl" (parent := "uake") (lean := "AKE.UAKE.opImpl")
$`\todo`
::::

:::defTitle "uake_oracle_impl" "Oracle implementation"
:::

::::definition "uake_oracle_impl" (parent := "uake") (lean := "AKE.UAKE.oracleImpl")
$`\todo`
::::

:::defTitle "uake_adversary" "UAKE adversary"
:::

::::definition "uake_adversary" (parent := "uake") (lean := "AKE.UAKE.Adversary")
$`\todo`
::::

:::defTitle "uake_ping_pong" "Ping-pong relaying"
:::

::::definition "uake_ping_pong" (parent := "uake") (lean := "AKE.UAKE.fullPingPong")
$`\todo`
::::

:::defTitle "uake_finalize" "Experiment finalization"
:::

::::definition "uake_finalize" (parent := "uake") (lean := "AKE.UAKE.finalize")
$`\todo`
::::

:::defTitle "uake_exp" "Security experiment"
:::

::::definition "uake_exp" (parent := "uake") (lean := "AKE.UAKE.Exp")
$`\todo`
::::

:::defTitle "uake_advantage" "UAKE advantage"
:::

::::definition "uake_advantage" (parent := "uake") (lean := "AKE.UAKE.advantage")
$`\todo`

::::
