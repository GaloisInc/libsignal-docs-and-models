import VersoManual
import VersoBlueprint

open Verso.Genre Manual

@[bib "PQXDH"]
def PQXDHSpec : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"The PQXDH Key Agreement Protocol"
  , authors := #[inlines!"Ehren Kret", inlines!"Rolfe Schmidt"]
  , journal := inlines!"Signal Specifications"
  , year := 2023
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , url := some "https://signal.org/docs/specifications/pqxdh/" }

@[bib "DF17"]
def DF17 : Verso.Genre.Manual.Bibliography.Citable := .inProceedings
  { title := inlines!"Unilaterally-Authenticated Key Exchange"
  , authors := #[inlines!"Yevgeniy Dodis", inlines!"Dario Fiore"]
  , year := 2017
  , booktitle := inlines!"Financial Cryptography and Data Security 2017"
  , url := some "https://eprint.iacr.org/2017/109" }

@[bib "LS17"]
def LS17 : Verso.Genre.Manual.Bibliography.Citable := .inProceedings
  { title := inlines!"No-Match Attacks and Robust Partnering Definitions: Defining Trivial Attacks for Security Protocols is Not Trivial"
  , authors := #[inlines!"Yong Li", inlines!"Sven Schäge"]
  , year := 2017
  , booktitle := inlines!"ACM CCS 2017"
  , url := some "https://eprint.iacr.org/2017/117" }

@[bib "BS23"]
def BS23 : Verso.Genre.Manual.Bibliography.Citable := .article
  { title := inlines!"A Graduate Course in Applied Cryptography"
  , authors := #[inlines!"Dan Boneh", inlines!"Victor Shoup"]
  , journal := inlines!"Online textbook (version 0.6)"
  , year := 2023
  , month := none
  , volume := inlines!""
  , number := inlines!""
  , url := some "https://toc.cryptobook.us/" }
