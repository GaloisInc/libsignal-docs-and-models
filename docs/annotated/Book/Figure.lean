import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual.Basic

open Verso ArgParse Doc Elab
open Verso.Doc.Elab
open Verso.Genre Manual

namespace Book.Figure

def figureCss := r#"
.book-figure {
  margin: 1.25rem 0;
  text-align: center;
}
.book-figure img {
  max-width: 100%;
  height: auto;
}
.book-figure > p { margin: 0; }
.book-figure figcaption {
  margin: 0.6rem auto 0;
  font-size: 0.9rem;
  color: #4b5563;
  text-align: left;
}
.book-figure figcaption > p:first-of-type { margin-top: 0; }
.book-figure figcaption > :last-child { margin-bottom: 0; }
"#

open Verso.Output Html in
def figureHtml (body : Html) (caption : Array Html) : Html :=
  let cap : Html :=
    if caption.isEmpty then .empty else {{<figcaption>{{caption}}</figcaption>}}
  {{<figure class="book-figure">{{body}}{{cap}}</figure>}}

end Book.Figure

namespace Verso.Genre.Manual

block_extension Block.bookFigure where
  traverse _ _ _ := pure none
  extraCss := [Book.Figure.figureCss]
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _ goB _ _ content => do
      pure <| .seq (← content.mapM goB)
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ content => do
      let rendered ← content.mapM goB
      match h : rendered.size with
      | 0 => pure .empty
      | _ + 1 => pure <| Book.Figure.figureHtml rendered[0] (rendered.extract 1)

@[directive]
def figure : DirectiveExpanderOf Unit
  | (), contents => do
    ``(Verso.Doc.Block.other Block.bookFigure #[$[$(← contents.mapM elabBlock)],*])

end Verso.Genre.Manual
