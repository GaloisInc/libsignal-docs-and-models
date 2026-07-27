import PQXDHDocs.Render
import PQXDHDocs.Chapters.MTP.Overview

def main (args : List String) : IO UInt32 :=
  PQXDHDocs.renderManual (%doc PQXDHDocs.Chapters.MTP.Overview) args
