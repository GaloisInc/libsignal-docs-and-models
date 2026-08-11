/-
Annotation roles for the libsignal-annotated book.

Two parallel commentary channels, each with three flavors:

  * `{galois}[...]`     — inline italic-pink emphasis (rare; for genuine in-line use)
  * `{galoisnote}[...]` — sidenote: a numbered pink superscript inline + the content
                          floated into the margin. Default choice for short Galois
                          commentary; visually offset without disturbing the spec
                          prose flow.
  * `:::galois`         — block-level annotation for paragraphs, code, multi-block

  * `{claude}[...]` / `{claudenote}[...]` / `:::claude` — identical triad, blue.

Channels are kept distinct so an audit pass can mechanically diff or strip
Claude commentary without touching Galois text.
-/

import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual.Basic

open Verso ArgParse Doc Elab
open Verso.Doc.Elab
open Verso.Genre Manual

namespace Book.Annotation

def annotationCss := r#"
/* ──── Inline italic emphasis (rare) ──── */
.annotation-galois { color: #a6105e; font-style: italic; }
.annotation-claude { color: #1d4ed8; font-style: italic; }

/* ──── Block annotation ──── */
.annotation-galois-block {
  border-left: 3px solid #a6105e;
  background: #fdf2f8;
  padding: 0.5rem 0.75rem;
  margin: 0.75rem 0;
  font-style: italic;
  color: #5b1339;
}
.annotation-galois-block::before {
  display: block; font-style: normal; font-weight: 600;
  font-size: 0.75rem; letter-spacing: 0.05em; text-transform: uppercase;
  color: #a6105e; margin-bottom: 0.25rem; content: "Galois";
}

.annotation-claude-block {
  border-left: 3px solid #1d4ed8;
  background: #eff6ff;
  padding: 0.5rem 0.75rem;
  margin: 0.75rem 0;
  font-style: italic;
  color: #1e3a8a;
}
.annotation-claude-block::before {
  display: block; font-style: normal; font-weight: 600;
  font-size: 0.75rem; letter-spacing: 0.05em; text-transform: uppercase;
  color: #1d4ed8; margin-bottom: 0.25rem; content: "Claude";
}

.annotation-galois-block > p:first-of-type,
.annotation-claude-block > p:first-of-type { margin-top: 0; }
.annotation-galois-block > :last-child,
.annotation-claude-block > :last-child { margin-bottom: 0; }

/* ──── Sidenotes (margin notes) ──── */
body { counter-reset: galois-note claude-note; }

.annotation-galois-note,
.annotation-claude-note { position: relative; }

.annotation-galois-note { counter-increment: galois-note; }
.annotation-claude-note { counter-increment: claude-note; }

.annotation-galois-note::after {
  content: counter(galois-note);
  color: #a6105e;
  font-size: 0.7em; font-weight: 700;
  vertical-align: super; margin: 0 0.1em;
}
.annotation-claude-note::after {
  content: counter(claude-note);
  color: #1d4ed8;
  font-size: 0.7em; font-weight: 700;
  vertical-align: super; margin: 0 0.1em;
}

.annotation-galois-note > .note,
.annotation-claude-note > .note {
  position: relative;
  padding: 0.5rem 0.75rem;
  font-size: 0.9em;
  font-style: italic;
  border-radius: 2px;
}
.annotation-galois-note > .note {
  background: #fdf2f8; border-left: 3px solid #a6105e; color: #5b1339;
}
.annotation-claude-note > .note {
  background: #eff6ff; border-left: 3px solid #1d4ed8; color: #1e3a8a;
}
.annotation-galois-note > .note::before {
  content: "G" counter(galois-note);
  display: block; font-style: normal; font-weight: 600;
  font-size: 0.65rem; letter-spacing: 0.05em; text-transform: uppercase;
  color: #a6105e; margin-bottom: 0.2rem;
}
.annotation-claude-note > .note::before {
  content: "C" counter(claude-note);
  display: block; font-style: normal; font-weight: 600;
  font-size: 0.65rem; letter-spacing: 0.05em; text-transform: uppercase;
  color: #1d4ed8; margin-bottom: 0.2rem;
}

/* Wide viewport: float note into the right margin */
@media screen and (min-width: 1400px) {
  .annotation-galois-note > .note,
  .annotation-claude-note > .note {
    float: right; clear: right;
    margin-right: -17rem; width: 14rem; margin-top: 0;
  }
}

/* Medium viewport */
@media screen and (max-width: 1400px) and (min-width: 701px) {
  .annotation-galois-note > .note,
  .annotation-claude-note > .note {
    float: right; clear: right;
    width: 38%; margin: 0.5rem 0 0.5rem 1rem;
  }
}

/* Narrow viewport (phone): inline below */
@media screen and (max-width: 700px) {
  .annotation-galois-note > .note,
  .annotation-claude-note > .note {
    display: block; width: 100%; margin: 0.5rem 0;
    float: none; clear: none;
  }
}

/* Hover affordance */
.annotation-galois-note:hover > .note { background: #fce7f3; }
.annotation-claude-note:hover > .note { background: #dbeafe; }
"#

open Verso.Output Html in
def inlineHtml (cls : String) (content : Html) : Html :=
  {{<span class={{cls}}>{{content}}</span>}}

open Verso.Output Html in
def blockHtml (cls : String) (content : Html) : Html :=
  {{<aside class={{cls}}>{{content}}</aside>}}

open Verso.Output Html in
def noteHtml (cls : String) (content : Html) : Html :=
  {{<span class={{cls}}><span class="note">{{content}}</span></span>}}

end Book.Annotation

namespace Verso.Genre.Manual

/-! ## Galois annotations -/

inline_extension Inline.galois where
  traverse _ _ _ := pure none
  extraCss := [Book.Annotation.annotationCss]
  toTeX :=
    open Verso.Output.TeX in
    some <| fun goI _ _ content => do
      let inner ← content.mapM goI
      pure <| .seq #[.raw "\\textit{", .seq inner, .raw "}"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ _ content => do
      Book.Annotation.inlineHtml "annotation-galois" <$> content.mapM goI

inline_extension Inline.galoisNote where
  traverse _ _ _ := pure none
  extraCss := [Book.Annotation.annotationCss]
  toTeX :=
    open Verso.Output.TeX in
    some <| fun goI _ _ content => do
      let inner ← content.mapM goI
      pure <| .seq #[.raw "\\textit{ [Galois note: ", .seq inner, .raw "]}"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ _ content => do
      Book.Annotation.noteHtml "annotation-galois-note" <$> content.mapM goI

block_extension Block.galois where
  traverse _ _ _ := pure none
  extraCss := [Book.Annotation.annotationCss]
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _ goB _ _ content => do
      let inner ← content.mapM goB
      let separated := inner.toList.intersperse (.raw "\n\n") |>.toArray
      pure <| .seq #[
        .raw "\\begin{quote}\n\\textbf{Galois.}\\itshape\n\n",
        .seq separated,
        .raw "\n\\end{quote}\n"
      ]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      Book.Annotation.blockHtml "annotation-galois-block" <$> content.mapM goB

/-- Inline italic-pink Galois emphasis. Rare; prefer `{galoisnote}` for short
    commentary or `:::galois` for paragraphs. -/
@[role]
def galois : RoleExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Inline.other Inline.galois #[$[$(← contents.mapM elabInline)],*])

/-- Galois sidenote: numbered pink superscript marker inline; content rendered
    in the margin. Default for short Galois commentary. -/
@[role]
def galoisnote : RoleExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Inline.other Inline.galoisNote #[$[$(← contents.mapM elabInline)],*])

/-- Block-level Galois commentary (paragraphs, code blocks). -/
@[directive galois]
def galoisBlock : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Block.other Block.galois #[$[$(← contents.mapM elabBlock)],*])

/-! ## Claude annotations -/

inline_extension Inline.claude where
  traverse _ _ _ := pure none
  extraCss := [Book.Annotation.annotationCss]
  toTeX :=
    open Verso.Output.TeX in
    some <| fun goI _ _ content => do
      let inner ← content.mapM goI
      pure <| .seq #[.raw "\\textit{", .seq inner, .raw "}"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ _ content => do
      Book.Annotation.inlineHtml "annotation-claude" <$> content.mapM goI

inline_extension Inline.claudeNote where
  traverse _ _ _ := pure none
  extraCss := [Book.Annotation.annotationCss]
  toTeX :=
    open Verso.Output.TeX in
    some <| fun goI _ _ content => do
      let inner ← content.mapM goI
      pure <| .seq #[.raw "\\textit{ [Claude note: ", .seq inner, .raw "]}"]
  toHtml :=
    open Verso.Output.Html in
    some <| fun goI _ _ content => do
      Book.Annotation.noteHtml "annotation-claude-note" <$> content.mapM goI

block_extension Block.claude where
  traverse _ _ _ := pure none
  extraCss := [Book.Annotation.annotationCss]
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _ goB _ _ content => do
      let inner ← content.mapM goB
      let separated := inner.toList.intersperse (.raw "\n\n") |>.toArray
      pure <| .seq #[
        .raw "\\begin{quote}\n\\textbf{Claude.}\\itshape\n\n",
        .seq separated,
        .raw "\n\\end{quote}\n"
      ]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      Book.Annotation.blockHtml "annotation-claude-block" <$> content.mapM goB

/-- Inline italic-blue Claude emphasis. Rare; prefer `{claudenote}` or `:::claude`. -/
@[role]
def claude : RoleExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Inline.other Inline.claude #[$[$(← contents.mapM elabInline)],*])

/-- Claude sidenote: numbered blue superscript marker inline; content in margin.
    Default for short Claude (audit / review) annotations. -/
@[role]
def claudenote : RoleExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Inline.other Inline.claudeNote #[$[$(← contents.mapM elabInline)],*])

/-- Block-level Claude commentary (paragraphs, code blocks). -/
@[directive claude]
def claudeBlock : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Block.other Block.claude #[$[$(← contents.mapM elabBlock)],*])
