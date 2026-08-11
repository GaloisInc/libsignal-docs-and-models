import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import PQXDHDocs.Bibliography
import PQXDHDocs.Chapters.Aeneas.Defs
import PQXDHDocs.Chapters.Aeneas.SimplifiedLemmas
import PQXDHDocs.Chapters.Aeneas.FullLemmas

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Aeneas-Extracted PQXDH" =>

*References:*

- {Informal.citet PQXDHSpec}[]
- {Informal.citet BAIFLibsignalVerify}[]

PQXDH as a UAKE, instantiated with the Aeneas-extracted implementation.

{include 1 PQXDHDocs.Chapters.Aeneas.Defs}

{include 1 PQXDHDocs.Chapters.Aeneas.SimplifiedLemmas}

{include 1 PQXDHDocs.Chapters.Aeneas.FullLemmas}

{blueprint_graph}

{blueprint_summary}
