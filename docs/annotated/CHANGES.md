# Port changes vs. Galois source

This file records every place this Verso port deviates from the source
markdown in `originals/`:

  - `originals/PQXDH-docs-to-code-ORIGINAL-2026-05-22.md`
  - `originals/SPQR-docs-to-code-ORIGINAL-2026-05-22.md`
  - `originals/triple-rachet-ORIGINAL-2026-07-17.md`

These changes are suitable for backporting to the Galois source documents.

## Conventions

- **Silent restore** — a Galois copy artifact (stray glyph, misspelling, missing
  punctuation) that doesn't represent intentional content. Removed silently in
  the port; the upstream Signal-spec wording is restored verbatim.
- **Marked correction** — Galois intentionally changed Signal's wording.
  Rendered with the `{galois}[…]` inline color in the port so a reader sees
  the substitution.

Every entry below is a silent restore unless tagged otherwise.

---

## PQXDH

### Intro paragraph (Book/PQXDH.lean)

| before | after | note |
|---|---|---|
| `tests/[pxdh.rs](http://pxdh.rs)` | `tests/[pqxdh.rs](https://github.com/GaloisInc/libsignal-testing/blob/tests/rust/protocol/tests/pqxdh.rs)` | Filename was `pxdh.rs`; correct file is `pqxdh.rs`. URL also corrected to point at the actual file rather than the placeholder `http://pxdh.rs`. |
| `Additionally, this tests creates` | `Additionally, this test creates` | Subject-verb agreement. |
| `exactly how libsignals realizes PQXDH` | `exactly how libsignal realizes PQXDH` | Extra `s`. |
| `The later case follows the same logic` | `The latter case follows the same logic` | Homophone confusion (later → latter). |

### Section 2.1 — PQXDH parameters table (Book/PQXDH/Preliminaries.lean)

| before | after | note |
|---|---|---|
| `ligsignal itself relies on` | `libsignal itself relies on` | Typo inside a Galois sidenote (curve row). |

### Section 2.5 — Post-Quantum Key Encapsulation Keys (Book/PQXDH/Preliminaries.lean)

The Galois source has the sentence "The pqkem public keys used within a PQXDH protocol run must all use the same pqkem parameter." **twice**:
  - once concatenated to the section opener with no separator (`public keys:The pqkem ...`), and
  - once after the table, on its own line.

Upstream Signal spec has the sentence only once, after the table. Removed the concatenated copy; kept the post-table sentence verbatim. A paragraph break was already present in the upstream layout.

### Section 3.2 — Publishing keys (Book/PQXDH/Protocol.lean)

| before | after | note |
|---|---|---|
| `Bob's curve identity key  IKB§` | `Bob's curve identity key  IKB` | Stray `§` after `IKB`. Upstream Signal spec has just `IKB`. |

### Section 3.3 — Sending the initial message, *Note* block (Book/PQXDH/Protocol.lean)

| before | after | note |
|---|---|---|
| `ciphertexts are actual serialized differently` | `ciphertexts are actually serialized differently` | Adverb form (Galois note text). |

---

## SPQR (ML-KEM Braid)

### Section 2.2 — Parameters (Book/SPQR/Protocol.lean)

| before | after | note |
|---|---|---|
| `using libcrus` | `using libcrux` | Library name typo — the crypto library is `libcrux` (github.com/cryspen/libcrux). |
| `Size of MAC's output, in byte.` | `Size of MAC's output, in bytes.` | Upstream Signal spec is "in bytes" (plural). |

### Section "Note on libsignal's code structure" — Rust comment in code example (Book/SPQR/CodeStructure.lean)

| before | after | note |
|---|---|---|
| `a more granulare version` | `a more granular version` | Typo in Galois-authored Rust comment. |

### Section 3.5 — Encoder domain size (Book/SPQR/Security.lean)

| before | after | note |
|---|---|---|
| `This is what libsignals SPQR uses itself` | `This is what libsignal's SPQR uses itself` | Possessive apostrophe (Galois note text). |

---

## Triple Ratchet

### Silent copy edits

| before | after | note |
|---|---|---|
| `one another other` | `one another` | Duplicated word. |
| `epoche` / `epoches` | `epoch` / `epochs` | Correct protocol terminology. |
| `mixes the the` | `mixes the` | Duplicated word. |
| `Alice initial SPQR state` | `Alice's initial SPQR state` | Missing possessive. |
| `Alice is one "epoche" ahead` | `Alice is one epoch ahead` | Correct terminology and unnecessary quotation marks. |
| `previous epochs message` | `previous epoch's message` | Missing possessive. |
| `Signal related papers` | `Signal-related papers` | Compound adjective. |

### Visible semantic corrections

The Triple Ratchet note is Galois-authored synthesis rather than copied Signal
specification prose. Its prose remains in `:::galois` blocks. Where validation
required a semantic correction, the replacement is visibly marked with the
`{claude}[…]` role and an adjacent `:::claude` block explains it:

| source wording | port treatment | reason |
|---|---|---|
| SPQR mixes in key material "after a certain period of time" and produces a fresh key only after an "epoch of time" | `{claude}` states that messages drive SPQR through the transitions that emit epoch secrets and make them mutually usable, and that each party emits at most one fresh secret per epoch. | SPQR advancement is message-driven, not controlled by a wall-clock timer or delayed until both parties have completed an epoch. |
| Sender reaches `Ct1Sampled`; receiver reaches `EkCt1Received` | The precise emitting transitions are marked in `{claude}`: `HeaderReceived → Ct1Sampled` on send and `EkSentCt1Received → NoHeaderReceived` on receive. | `EkCt1Received` is not an implementation state, and merely being in `Ct1Sampled` does not describe both emission paths. |
| Triple Ratchet reuses the "current" or "pre-existing SPQR key" | The source wording is retained as a quotation and `{claude}` explains that SPQR derives a distinct per-message key from the selected epoch chain. | The public SPQR API returns a per-message chain key, not the raw epoch secret. |
| Receive lookup uses the message epoch | `{claude}` records the actual lookup as `scka_msg.epoch - 1` plus the chain index. | Matches the pinned receive implementation. |

### Audit notes and retained TODOs

- The source's speculation about sender-side epoch indexing remains in the
  Galois text. An adjacent Claude block explains the ML-KEM Braid
  `sending_epoch` contract and why `msg.epoch - 1` is intentional.
- The source's epoch-sized vulnerable-set conclusion is quoted in a Claude
  audit block rather than retained as factual Galois prose. The cited
  specification says the minimum depends on protocol parameters, the realized
  size depends on messaging behavior, and the maximum is unbounded.
- All four source TODOs remain in `Book/TripleRatchet/Todo.lean`. The indexing
  question has an adjacent audit resolution; key-retention and state-loss
  questions remain open.

### Structural and reference changes

- The source is split into a thin `Book/TripleRatchet.lean` root plus
  `Overview`, `Protocol`, `Security`, and `Todo` subdocuments, matching the
  PQXDH/SPQR chapter idiom.
- Source material described as "colored in blue" is represented by Verso
  citations. Blue remains reserved for Claude audit annotations.
- Broad source links were narrowed to the statements they support. The
  repository-first roles `{libsignal57d}` and `{spqrf258}` preserve the source's
  newer pinned commits without changing the revisions used by PQXDH and SPQR.

---

## Structural / styling changes

These are markup re-shapings rather than text corrections; they don't need to be
backported to the source markdown but are recorded for completeness.

### Galois additions → sidenotes

In the Galois source, asides and code-references were inline parentheticals or
bracket-wrapped links interleaved with Signal prose. In the port these are
expressed as `{galoisnote}[…]` sidenotes, so the Signal-text flow stays clean
and Galois additions appear in the margin. Affected patterns:

- `(see [path](url))` — parenthetical code-ref → `{galoisnote}[{repo "path"}[]]`
- `\[see refA, refB\]` — bracketed list of code-refs → sidenote with the refs
- `\[see ref for X\]` — bracket + descriptive context → sidenote with the descriptive text

### Galois continuation prose → inline `{galois}` (pink italic)

Galois clauses that **continue or extend** a Signal sentence (rather than
asides) are kept inline and color-coded, e.g.:

  > Alice verifies the signatures on the prekeys *and checks that Bob's address
  > and key are trusted* [ref].

The italic span is rendered inline pink in the port via `{galois}[…]`. Affected:

- Book/PQXDH/Protocol.lean §3.3 — Galois prefix "Alice processes the prekey_bundle they receive from the server [ref] and" and continuation "and checks that Bob's address and key are trusted [ref]".

### Code-ref URL → role roles

All `[label](https://github.com/signalapp/libsignal/blob/7c8cb0c…/…)` links to the
three pinned commits (libsignal `7c8cb0c5fce…`, SparsePostQuantumRatchet
`46e38745…`, GaloisInc/libsignal-testing `5400d962…`) were migrated to the
`{libsignal "path"}[]` / `{spqr "path"}[]` / `{galoistest "path"}[]` inline
roles. URL prefixes are pinned once in `Book/CodeRef.lean`; updating the commit
is a single edit.

---

## Audit-driven code-ref corrections

After tagging, every code-ref was independently verified against the source at
its pinned commit (3 parallel subagents, then double-checked by hand). 10 of
141 refs had issues; the clerical ones were corrected in the port and are
listed here. Four nuanced findings carry `{claudenote}` annotations explaining
spec↔implementation gaps instead of silent edits.

### PQXDH

| Port location | Issue | Fix |
|---|---|---|
| `Book/PQXDH/Preliminaries.lean` §2.1 (EncodeKEM row) | Cited `libsignal/rust/protocol/src/kem.rs#L319-L331`, which is `deserialize()` (decode). | Swapped to `#L333-L338` (`serialize()`). |
| `Book/PQXDH/Preliminaries.lean` §2.1 (DecodeKEM row) | Cited `libsignal/rust/protocol/src/kem.rs#L333-L338`, which is `serialize()` (encode). | Swapped to `#L319-L331` (`deserialize()`). |
| `Book/PQXDH/Protocol.lean` §3.2 (Bob's identity-key bullet) | Cited `galoistest/rust/protocol/tests/pqxdh.rs#L27`, but L27 is `alice_store_builder = TestStoreBuilder::new()` (Alice). Bob is at L26. | Changed `#L27` → `#L26`. |
| `Book/PQXDH/Protocol.lean` §3.3 (Bob-side `*Note*` block) | Claimed `session.rs#L166` is "part of `fn message_decrypt_prekey()`". L166 is in `fn process_prekey_impl` (`message_decrypt_prekey` lives in `session_management.rs:202` and calls `process_prekey_impl` via `session::process_prekey`). | Updated prose: "part of `fn message_decrypt_prekey()` and the `fn process_prekey_impl()` it calls". Both refs retained. |

### SPQR

| Port location | Issue | Fix |
|---|---|---|
| `Book/SPQR/Protocol.lean` §2.3 (Messages, `epoch` field) | Cited `pq_ratchet.proto#L196`, but L196 is `message Epoch` inside `Chain` (chain state struct), not the per-wire-message epoch. | Changed `#L196` → `#L46` (`V1Msg.epoch`). |
| `Book/SPQR/Protocol.lean` §2.5 (*EkReceivedCt1Sampled*) | Cited `send_ek.rs#L195-L234`, which is `impl EkSentCt1Received::recv_ct2_chunk` (different state, send_ek side). | Changed to `send_ct.rs#L241-L249` — `impl EkReceivedCt1Sampled::recv_ct1_ack`. |

### Nuanced findings (flagged with `{claudenote}` rather than silently fixed)

| Port location | Note |
|---|---|
| `Book/PQXDH/Protocol.lean` §3.4 (Bob deletes DH/SS values) | `pqxdh.rs:375` is `Ok(HandshakeKeys::derive(&secrets))` — the function return. "Deletion" is implicit via Rust drop at scope exit; no explicit zeroize at that line. |
| `Book/SPQR/Protocol.lean` §2.2 (`decoder.has_message()`) | `has_message()` does not exist in libsignal/SPQR. The cited `polynomial.rs:748` is `fn necessary_points(...)`, a private helper. libsignal collapses the spec's `has_message()` + `message()` into one `decoded_message() → Option<Vec<u8>>` at `polynomial.rs:860`. |
| `Book/SPQR/Protocol.lean` §2.2 (`KDF_AUTH` IKM = `update_key`) | Cited line is the output-split assignment. The real IKM in libsignal at `authenticator.rs:45` is `root_key ‖ update_key` — i.e. the implementation differs from the spec's abstraction. |
| `Book/SPQR/Protocol.lean` §2.2 (`KDF_AUTH` salt = `root_key`) | Cited line is the output split. The real HKDF call at `authenticator.rs:51` passes `&[0u8; 32]` as the salt; root_key is folded into IKM instead. In code, salt = zero and IKM = root_key‖update_key, not the spec's salt = root_key and IKM = update_key. |
