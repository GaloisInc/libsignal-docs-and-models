import PQXDHDocs.Render
import PQXDHDocs.Chapters.UAKE.Overview

def main (args : List String) : IO UInt32 :=
  PQXDHDocs.renderManual (%doc PQXDHDocs.Chapters.UAKE.Overview) args
