import VersoManual
import Book.Annotation

open Verso.Genre Manual

#doc (Manual) "TODO" =>

:::galois
- Figure out key deletion and memory management
- Figure out the interaction between users and server (this is handled outside of Rust)
- Figure out where the last resort key is created and handled since libsignal itself does not distinguish between that kinds of key and the other one time keys.
- Figure out what signal does to check that an identity is trusted
:::
