/-
A `rust` code-block handler for the book.

Usage in `.lean` source:

    ```rust
    pub struct Foo { ... }
    ```

Renders as `<pre class="code-rust"><code class="language-rust">…</code></pre>` —
the standard hook a client-side highlighter (highlight.js, Prism, etc.) picks
up. The `Book.RustCode.css` stylesheet provides default styling (monospace,
tinted background, bordered) so the block still looks like code without any
highlighter loaded.
-/

import Lean.Data.Json
import Verso
import Verso.Doc.ArgParse
import Verso.Doc.Elab.Monad
import VersoManual.Basic

open Lean
open Verso ArgParse Doc Elab
open Verso.Doc.Elab
open Verso.Genre Manual

namespace Book.RustCode

def css := r#"
.code-rust {
  background: #f8fafc;
  border: 1px solid #e2e8f0;
  border-radius: 4px;
  padding: 0.75rem 1rem;
  overflow-x: auto;
  font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace;
  font-size: 0.85em;
  line-height: 1.5;
  color: #1e293b;
  margin: 0.75rem 0;
}
.code-rust > code.language-rust {
  background: transparent;
  padding: 0;
  font-family: inherit;
  font-size: inherit;
  color: inherit;
  white-space: pre;
}
"#

/-- Self-bootstrap highlight.js from a CDN on page load and run it over every
    `.code-rust .language-rust` block. Lightweight client-side highlighting;
    fails silently if the network is unavailable. -/
def bootstrapJs := r#"
(function () {
  if (window.__rustHljsBootstrapped) return;
  window.__rustHljsBootstrapped = true;
  var link = document.createElement('link');
  link.rel = 'stylesheet';
  link.href = 'https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/styles/github.min.css';
  document.head.appendChild(link);
  var s = document.createElement('script');
  s.src = 'https://cdnjs.cloudflare.com/ajax/libs/highlight.js/11.9.0/highlight.min.js';
  s.onload = function () {
    if (window.hljs) {
      document.querySelectorAll('.code-rust code.language-rust').forEach(function (el) {
        window.hljs.highlightElement(el);
      });
    }
  };
  document.head.appendChild(s);
})();
"#

end Book.RustCode

namespace Verso.Genre.Manual

block_extension Block.rustCode (code : String) where
  data := ToJson.toJson code
  traverse _ _ _ := pure none
  extraCss := [Book.RustCode.css]
  extraJs := [Book.RustCode.bootstrapJs]
  toTeX :=
    open Verso.Output.TeX in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error _ => pure .empty
      | .ok (c : String) =>
        pure (.seq #[.raw "\\begin{verbatim}\n", .raw c, .raw "\n\\end{verbatim}"])
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error _ => pure .empty
      | .ok (c : String) =>
        pure {{<pre class="code-rust"><code class="language-rust">{{c}}</code></pre>}}

/-- A code block tagged ` ```rust `, rendered as `<pre><code class="language-rust">…</code></pre>`. -/
@[code_block]
def rust : CodeBlockExpanderOf Unit
  | (), str => do
    ``(Doc.Block.other (Block.rustCode $(quote str.getString)) #[])
