# PQXDH

Formal verification of Signal's PQXDH key-agreement protocol in Lean 4, built on top of
[VCVio](https://github.com/Verified-zkEVM/VCV-io).

The development covers:

- A formalization in Lean of UAKE (unilaterally authenticated key exchange) from [DF'17](https://eprint.iacr.org/2017/109.pdf).
- A Lean implementation of the PQXDH spec, instantiated as a UAKE protocol and associated correctness and security proofs.
- An Aeneas-extracted model of the reference PQXDH implementation, instantiated as a UAKE protocol and associated correctness and security proofs.

Reference papers are collected under [`PQXDH/docs`](PQXDH/docs), including the Signal PQXDH
specification and the underlying UAKE literature.

## Layout

- `PQXDH/`: the protocol (`Spec`, `Aeneas`) formalizations.
- `ToVCVio/`: additions to VCVio relied on by `PQXDH`, staged for upstreaming, including security definition (`UAKE`).
- `docs/`: Verso documentation of our PQXDH and UAKE models.

## License

Apache-2.0.
