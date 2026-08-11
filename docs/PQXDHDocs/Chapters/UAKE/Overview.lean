import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import PQXDHDocs.Bibliography
import PQXDHDocs.Chapters.UAKE.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "The UAKE Model" =>

*References:*

- {Informal.citet DF17}[]

The unilaterally-authenticated key exchange model shared by all three PQXDH realizations.

{include 1 PQXDHDocs.Chapters.UAKE.Defs}

{blueprint_graph}

{blueprint_summary}
