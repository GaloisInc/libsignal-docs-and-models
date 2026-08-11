/-
Code-location reference roles.

  * `{libsignal "rust/protocol/src/foo.rs#L10-L20"}`
  * `{spqr     "src/v1/chunked/states.rs#L41"}`
  * `{galoistest "rust/protocol/tests/pqxdh.rs#L27"}`
  * `{libsignal57d "rust/protocol/src/triple_ratchet.rs#L93-L104"}`
  * `{spqrf258 "src/lib.rs#L294-L299"}`

Each role takes a positional string argument — a repository-relative path
with an optional line-range fragment — and renders as a compact
"➤ parent/file:lines" badge linking to the corresponding GitHub URL. The
repository commit is pinned in this file so updates happen in one place.

Display rules:
  * `rust/protocol/src/pqxdh.rs#L79-L92`         → `src/pqxdh.rs:79-92`
  * `rust/protocol/tests/support/mod.rs#L226`    → `support/mod.rs:226`
  * `src/v1/chunked/send_ek.rs#L82C1-L98C6`      → `chunked/send_ek.rs:82-98`
  * `src/v1`                                      → `src/v1`
-/

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual.Basic

open Lean
open Verso ArgParse Doc Elab
open Verso.Doc.Elab
open Verso.Genre Manual

namespace Book.CodeRef

structure PathArg where
  path : String

section
variable [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadFileMap m]

def PathArg.parse : ArgParse m PathArg :=
  PathArg.mk <$> .positional `path .string

instance : FromArgs PathArg m where
  fromArgs := PathArg.parse

end

def libsignalBase  : String := "https://github.com/signalapp/libsignal/blob/7c8cb0c5fce1d01805199de992bf4323f4765f1f"
def spqrBase       : String := "https://github.com/signalapp/SparsePostQuantumRatchet/blob/46e387458d438b81a3485e26bf6bb44595e52073"
def galoistestBase : String := "https://github.com/GaloisInc/libsignal-testing/blob/5400d9626090d7bfa83f89248e1d78558277bf6f"
def libsignal57dBase : String := "https://github.com/signalapp/libsignal/blob/57d41c877d5a55d881fb3f52d9b16900118ee29b"
def spqrF258Base : String := "https://github.com/signalapp/SparsePostQuantumRatchet/blob/f2589fef855c10f39d72634dab3d14654dd410bf"

/-- Convert a GitHub line fragment to a clean line range:
    `L79-L92`           → `79-92`
    `L34`               → `34`
    `L82C1-L98C6`       → `82-98`  (column info stripped)
-/
def parseLineRange (s : String) : String :=
  let parts := s.splitOn "-"
  let cleanParts := parts.map fun p =>
    let stripL := if p.startsWith "L" then (p.drop 1).toString else p
    -- Drop any column suffix `C<n>`
    (stripL.splitOn "C")[0]!
  String.intercalate "-" cleanParts

/-- Escape characters that are special in LaTeX (notably `#` and `%`) so a
    URL containing them can safely appear inside `\href{…}{…}`. -/
def texEscapeUrl (s : String) : String :=
  s.replace "\\" "\\\\"
   |>.replace "#" "\\#"
   |>.replace "%" "\\%"
   |>.replace "{" "\\{"
   |>.replace "}" "\\}"

/-- Escape characters that are special in LaTeX text mode (`_`, `#`, `%`,
    `&`, `$`, `~`, `^`) so a path label can safely appear inside `\texttt{…}`.
    `\texttt` only changes font; it does NOT disable category codes. -/
def texEscapeLabel (s : String) : String :=
  s.replace "\\" "\\textbackslash{}"
   |>.replace "_" "\\_"
   |>.replace "#" "\\#"
   |>.replace "%" "\\%"
   |>.replace "&" "\\&"
   |>.replace "$" "\\$"
   |>.replace "{" "\\{"
   |>.replace "}" "\\}"
   |>.replace "~" "\\textasciitilde{}"
   |>.replace "^" "\\textasciicircum{}"

/-- Derive the visible badge label from a repo-relative path.
    Shows the last two path segments plus the line range, which gives enough
    context to disambiguate generic filenames like `mod.rs` without being
    verbose. -/
def pathLabel (path : String) : String :=
  let hashSplit := path.splitOn "#"
  let filePart := hashSplit[0]!
  let segments := filePart.splitOn "/"
  let n := segments.length
  let displayPath :=
    if n ≥ 2 then segments[n-2]! ++ "/" ++ segments[n-1]!
    else filePart
  match hashSplit[1]? with
  | some lineSpec => displayPath ++ ":" ++ parseLineRange lineSpec
  | none => displayPath

def css := r#"
.code-ref {
  font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
  font-size: 0.82em;
  background: #f3f4f6;
  border: 1px solid #d1d5db;
  border-radius: 3px;
  padding: 0 0.35rem;
  white-space: nowrap;
  color: #1f2937;
  text-decoration: none;
  margin: 0 0.05rem;
}
.code-ref:hover { background: #e5e7eb; text-decoration: none; }
.code-ref-icon { color: #6366f1; margin-right: 0.25rem; font-weight: 600; }
.code-ref-libsignal  { border-left: 3px solid #6366f1; }
.code-ref-libsignal .code-ref-icon  { color: #6366f1; }
.code-ref-spqr       { border-left: 3px solid #0ea5e9; }
.code-ref-spqr .code-ref-icon       { color: #0ea5e9; }
.code-ref-galoistest { border-left: 3px solid #16a34a; }
.code-ref-galoistest .code-ref-icon { color: #16a34a; }
"#

end Book.CodeRef

namespace Verso.Genre.Manual

inline_extension Inline.codeRef (url : String) (cls : String) (label : String) where
  data := ToJson.toJson (url, cls, label)
  traverse _ _ _ := pure none
  extraCss := [Book.CodeRef.css]
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _ _ data _content => do
      match FromJson.fromJson? data with
      | .error _ => pure .empty
      | .ok ((u, _, l) : String × String × String) =>
        let uEsc := Book.CodeRef.texEscapeUrl u
        let lEsc := Book.CodeRef.texEscapeLabel l
        pure (.raw s!"\\href\{{uEsc}}\{\\texttt\{{lEsc}}}")
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _content => do
      match FromJson.fromJson? data with
      | .error _ => pure .empty
      | .ok ((u, c, l) : String × String × String) =>
        let cls := "code-ref " ++ c
        pure {{<a href={{u}} class={{cls}}><span class="code-ref-icon">"➤"</span>{{l}}</a>}}

/-- Code-location reference into the signalapp/libsignal repo. -/
@[role]
def libsignal : RoleExpanderOf Book.CodeRef.PathArg
  | { path }, _ => do
    let url := Book.CodeRef.libsignalBase ++ "/" ++ path
    let label := Book.CodeRef.pathLabel path
    ``(Doc.Inline.other (Inline.codeRef $(quote url) "code-ref-libsignal" $(quote label))
        #[Doc.Inline.text $(quote label)])

/-- Code-location reference into the signalapp/SparsePostQuantumRatchet repo. -/
@[role]
def spqr : RoleExpanderOf Book.CodeRef.PathArg
  | { path }, _ => do
    let url := Book.CodeRef.spqrBase ++ "/" ++ path
    let label := Book.CodeRef.pathLabel path
    ``(Doc.Inline.other (Inline.codeRef $(quote url) "code-ref-spqr" $(quote label))
        #[Doc.Inline.text $(quote label)])

/-- Code-location reference into the GaloisInc/libsignal-testing repo. -/
@[role]
def galoistest : RoleExpanderOf Book.CodeRef.PathArg
  | { path }, _ => do
    let url := Book.CodeRef.galoistestBase ++ "/" ++ path
    let label := Book.CodeRef.pathLabel path
    ``(Doc.Inline.other (Inline.codeRef $(quote url) "code-ref-galoistest" $(quote label))
        #[Doc.Inline.text $(quote label)])

/-- Code-location reference into libsignal revision 57d41c8. -/
@[role]
def libsignal57d : RoleExpanderOf Book.CodeRef.PathArg
  | { path }, _ => do
    let url := Book.CodeRef.libsignal57dBase ++ "/" ++ path
    let label := Book.CodeRef.pathLabel path
    ``(Doc.Inline.other (Inline.codeRef $(quote url) "code-ref-libsignal" $(quote label))
        #[Doc.Inline.text $(quote label)])

/-- Code-location reference into SparsePostQuantumRatchet revision f2589fe. -/
@[role]
def spqrf258 : RoleExpanderOf Book.CodeRef.PathArg
  | { path }, _ => do
    let url := Book.CodeRef.spqrF258Base ++ "/" ++ path
    let label := Book.CodeRef.pathLabel path
    ``(Doc.Inline.other (Inline.codeRef $(quote url) "code-ref-spqr" $(quote label))
        #[Doc.Inline.text $(quote label)])
