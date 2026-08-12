import VersoManual
import Book

open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  manualMain (%doc Book) (options := args)
    (config := { extraFiles := [("docs/annotated/static", "static")] })
