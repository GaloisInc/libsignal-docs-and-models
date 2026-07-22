# PQXDH

Formal verification of Signal's PQXDH key-agreement protocol in Lean 4, built on top of
[VCVio](https://github.com/Verified-zkEVM/VCV-io).

The development covers:

- Interactive message-transmission security games (iCCA, iCMA).
- A unilaterally-authenticated key exchange (UAKE) spec and its security reduction.
- An Aeneas-extracted model of the reference PQXDH implementation.

Reference papers are collected under [`PQXDH/docs`](PQXDH/docs), including the Signal PQXDH
specification and the underlying UAKE literature.

## Layout

- `PQXDH/` — the protocol formalization (`Spec`, `MTP`, `HardnessAssumptions`, `Aeneas`).
- `ToVCVio/` — additions to VCVio relied on by `PQXDH`, staged for upstreaming.

## License

Apache-2.0.
