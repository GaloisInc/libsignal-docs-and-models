# libsignal-verso

A [Verso](https://github.com/leanprover/verso) port of Galois's annotated
versions of two Signal protocol specifications and an implementation-focused
chapter connecting them:

  - **PQXDH** — Post-Quantum Extended Diffie-Hellman key agreement
    ([upstream spec](https://signal.org/docs/specifications/pqxdh/))
  - **SPQR** — Sparse Post-Quantum Ratchet, a.k.a. the ML-KEM Braid protocol
    ([upstream spec](https://signal.org/docs/specifications/mlkembraid/))
  - **Triple Ratchet** — how libsignal combines the Double Ratchet and SPQR
    after PQXDH session establishment

The port preserves Signal's upstream spec prose verbatim and tags every Galois
annotation so the document can be mechanically stripped back to upstream.
Code-location references into the libsignal Rust implementation are
commit-pinned and render as compact monospace badges.

## Build

```bash
lake update   # once, fetches Verso (commit-pinned in lakefile)
lake build
lake exe generate
```

Output lands in `_out/html-multi/`. Verso emits a multi-page static site; serve
with any HTTP server to view (directory-style URLs don't resolve under
`file://`):

```bash
python3 -m http.server -d _out/html-multi 8000
# then open http://localhost:8000/
```

## Layout

```
Book.lean                  root document; bibliography citations; chapter includes
Book/
  Annotation.lean          {galois}/{galoisnote}/:::galois  + {claude} triad (roles)
  CodeRef.lean             repository- and revision-pinned code-reference roles
  Papers.lean              bibliography entries for Signal sources and papers
  PQXDH.lean               PQXDH chapter root
  PQXDH/
    Preliminaries.lean     §2 parameters, EC keys, post-quantum KEM keys
    Protocol.lean          §3 publish / send / receive
    Todo.lean              Galois open questions
  SPQR.lean                SPQR/ML-KEM Braid chapter root
  SPQR/
    CodeStructure.lean     Galois-authored note on the libsignal repo layout
    Protocol.lean          §2 overview, parameters, messages, internal auth, state machine
    Security.lean          §3 vulnerable message set, PCS note, encoder, epochs
  TripleRatchet.lean       Triple Ratchet chapter root
  TripleRatchet/
    Overview.lean          high-level description; PQXDH handoff
    Protocol.lean          Triple Ratchet send/receive paths
    Security.lean          vulnerable message set
    Todo.lean              Galois open questions and audit resolutions
Main.lean                  Verso `manualMain` entry point
lakefile.toml              Lake config; pins Verso v4.29.0
lean-toolchain             Lean 4.29.0
lake-manifest.json         pinned dependency commits
CHANGES.md                 text-level deviations from the Galois source markdown
```

## Annotation conventions

All Galois additions to Signal text are tagged. Three flavors per channel:

| Markup | Use | Render |
|---|---|---|
| `{galois}[…]` | Continuation prose extending a Signal sentence | inline pink italic |
| `{galoisnote}[…]` | Aside / cross-reference / code-pointer | numbered superscript + margin note |
| `:::galois … :::` | Paragraph, code excerpt, or whole-chapter commentary | bordered block, "GALOIS" label |

The parallel triad `{claude}` / `{claudenote}` / `:::claude` (blue) is reserved
for Claude-generated audit / review annotations and is kept on a separate
channel so the audit pass can be added, reviewed, or stripped independently.

## Code-location references

Five commit-pinned roles for pointing at specific lines in upstream Rust:

| Role | Repo | Pinned commit |
|---|---|---|
| `{libsignal "path#L1-L5"}[]` | signalapp/libsignal | `7c8cb0c5fce…` |
| `{spqr "path#L1-L5"}[]` | signalapp/SparsePostQuantumRatchet | `46e387458d…` |
| `{galoistest "path#L1"}[]` | GaloisInc/libsignal-testing | `5400d96260…` |
| `{libsignal57d "path#L1"}[]` | signalapp/libsignal | `57d41c877d…` |
| `{spqrf258 "path#L1"}[]` | signalapp/SparsePostQuantumRatchet | `f2589fef85…` |

These render as `[➤ parent/file:lines]` badges; revision-specific pins live in
`Book/CodeRef.lean` (one-edit updates).

## Source materials

The Galois annotated markdown, Triple Ratchet notes, and upstream Signal PDFs
are kept locally under `originals/` and not committed. See `CHANGES.md` for every typographic
correction this port made against the Galois source — these are suitable for
backporting to the source markdown.

## Status

The port preserves the Galois doc's section structure. Deliberate omissions
from upstream Signal (per the Galois intro): PQXDH §1, §2.2, §2.3, §4; SPQR
chapter 1, §2.6, much of chapter 3, all upstream pseudocode, and the
state-machine diagram. See the in-chapter `:::claude` audit blocks for
independently added validation and corrections.
