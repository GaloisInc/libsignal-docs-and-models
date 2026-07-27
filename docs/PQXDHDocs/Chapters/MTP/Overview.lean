import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import PQXDHDocs.Bibliography
import PQXDHDocs.Chapters.MTP.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Message-Transmission Protocol" =>

*References:*

- {Informal.citet DF17}[]

This chapter is a documentation scaffold for the interactive message-transmission
games (iCCA, iCMA) and their theorems. The prose below is a placeholder pending
write-up.

{include 1 PQXDHDocs.Chapters.MTP.Defs}

{blueprint_graph}

{blueprint_summary}
