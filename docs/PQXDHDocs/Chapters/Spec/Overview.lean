import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import PQXDHDocs.Bibliography
import PQXDHDocs.Chapters.Spec.Defs
import PQXDHDocs.Chapters.Spec.Lemmas

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "PQXDH Protocol Specification" =>

*References:*

- {Informal.citet PQXDHSpec}[]
- {Informal.citet DF17}[]

PQXDH is modeled as a DF'17-style UAKE.

{include 1 PQXDHDocs.Chapters.Spec.Defs}

{include 1 PQXDHDocs.Chapters.Spec.Lemmas}

{blueprint_graph}

{blueprint_summary}
