Live Verso documentation site here: https://galoisinc.github.io/libsignal-docs-and-models/

# LibSignal Documentation

Verso documentation for the SPQR, Tripple Ratchet, and PQXDH implementations in [LibSignal](https://github.com/signalapp/libsignal).

# PQXDH Models

Formal verification of Signal's PQXDH key-agreement protocol in Lean 4, built on top of
[VCVio](https://github.com/Verified-zkEVM/VCV-io).

The goal of this effort was to state (and ideally prove) game-based cryptographic security definitions stated using VCV-io directly on models of the LibSignal Rust code, extracted using Aeneas. In order to do this, I first wrote a model of the unilaterally authenticated key exchange security notion from [DF'17](https://eprint.iacr.org/2017/109.pdf). Then I used two Aeneas-extracted code models to instantiate UAKE schemes and state a bound for each on adversarial advantage in the UAKE security game. Our UAKE definition is being considered for upstreaming into VCV-io (PR [here](https://github.com/Verified-zkEVM/VCVio/pull/476)).

Another goal was to avoid security proofs that are heavily dependent on the specific Rust implementation, so the proofs could be reused for multiple implementations. To this end, I also hand-wrote an implementation of PQXDH based on [the spec](https://signal.org/docs/specifications/pqxdh), along with UAKE correctness and security theorems. (The correctness theorems on the spec have proofs, but the security theorems are currently sorry'd.) Rather than trying to directly prove UAKE security on the extracted implementations, I had Claude use a game-hop to the spec-based implementation. These game hops were relatively easy for Claude to prove automatically, as opposed to the proofs for the spec. Ideally, a change to the code and the corresponding Aeneas-extracted model would only touch these game-hops, making the proofs easily repairable.

The development covers:

- A formalization in Lean of UAKE (unilaterally authenticated key exchange) from [DF'17](https://eprint.iacr.org/2017/109.pdf).
- A Lean implementation of the [PQXDH spec](https://signal.org/docs/specifications/pqxdh), instantiated as a UAKE protocol, along with correctness proofs and (sorry'd) security theorems.
- Two Aeneas-extracted code models of the PQXDH implementation and security proofs reducing to the spec.
  + `PQXDH/Aeneas/Simplified/`: A model of a simplified Rust implementation based on the original LibSignal code, produced by Mike Dodds [here](https://github.com/septract/aeneas-vcvio-demos).
  + `PQXDH/Aeneas/Full/`: A model high-fidelity model of the LibSignal implementation extracted by Oliver at BAIF [here](https://github.com/Beneficial-AI-Foundation/libsignal-verify).

Reference papers are collected under [`PQXDH/docs`](PQXDH/docs), including the Signal PQXDH
specification and the underlying UAKE literature.

## AI Usage

I used Claude-code in developing these Lean models and proofs in three different ways:

- **Security definitions, PQXDH spec model, and security theorems:** Human-written code. These are delicate definitions that are part of the trust-base of the project. I initially experimented with using Claude to define these, but I found that it tended to simplify things in ways that had significant security ramifications. The workflow I landed on eventually was to write the definitions myself, and then have Claude check my work for fidelity to the papers e.g., by generating small examples or cross-referencing my definitions and comments with the paper. I was also able to use Claude for small mechanical changes here.
- **UAKE instantiations:** Highly supervised AI-written code. In this case, the task in Lean was mostly mechanical, and small enough that I could tractably check it by hand. I was able to have Claude write most of the defnitions and carefully supervise the result.
- **Proof-internal Lean code:** I was able to offload this almost entirely onto Claude, with occasional suggestions from me. I restricted the code Claude was allowed to edit to the *Lemmas.lean files. In cases where Claude got stuck due to issues at the level of the model or theorem statement (e.g., when new hypotheses were needed or a bound needed to be loosened), I had it discuss the issue with me and then decided how to proceed.

## Layout

- `PQXDH/`: the protocol (`Spec`, `Aeneas`) formalizations.
- `ToVCVio/`: additions to VCVio relied on by `PQXDH`, staged for upstreaming, including security definition (`UAKE`).
- `docs/`: Verso documentation of our PQXDH and UAKE models.

## License

Apache-2.0.
