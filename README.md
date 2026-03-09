# Gasper Formal Verification in Lean 4

Mechanized proofs of safety and liveness properties for the [Gasper protocol](https://arxiv.org/abs/2003.03052) (Casper FFG + LMD GHOST), ported from [Rocq](https://github.com/runtimeverification/beacon-chain-verification/tree/master/casper/coq) to Lean 4 with mathlib4.

## Theorems

- **Accountable Safety** — Two conflicting blocks cannot both be finalized without slashing at least 1/3 of validators.
- **Plausible Liveness** — 2/3 honest validators can always finalize new blocks.
- **Slashable Bound** — Lower bound on slashable stake under dynamic validator sets.

## Build

```bash
lake exe cache get
lake build
```

Requires [Lean 4](https://leanprover.github.io/) v4.26.0.

## Acknowledgements

This project is a Lean 4 port of the [Beacon Chain Verification](https://github.com/runtimeverification/beacon-chain-verification/tree/master/casper/coq) project by [Runtime Verification, Inc.](https://runtimeverification.com/), originally written in Rocq (Coq).

## License

[Apache License 2.0](LICENSE)
