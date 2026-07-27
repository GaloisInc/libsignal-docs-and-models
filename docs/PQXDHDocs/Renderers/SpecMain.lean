import PQXDHDocs.Render
import PQXDHDocs.Chapters.Spec.Overview

def main (args : List String) : IO UInt32 :=
  PQXDHDocs.renderManual (%doc PQXDHDocs.Chapters.Spec.Overview) args
