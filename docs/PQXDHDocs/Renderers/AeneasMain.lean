import PQXDHDocs.Render
import PQXDHDocs.Chapters.Aeneas.Overview

def main (args : List String) : IO UInt32 :=
  PQXDHDocs.renderManual (%doc PQXDHDocs.Chapters.Aeneas.Overview) args
