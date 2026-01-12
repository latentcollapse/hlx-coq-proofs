# HLX Formal Verification

This repository contains the formal verification of the core HLX language axioms using the Rocq Prover (Coq 9.1).

## Axioms Proven

- **A1: Determinism** (Theorem in `Axioms.v` and `Compilation.v`)
- **A3: Injectivity** (Axiomatized in `Axioms.v`)
- **A4: Universal Value Representation** (Axiomatized in `Values.v`)

## Verification Log

See `PROOF_LOG.txt` for the timing and verification output of the latest build.

## Running Proofs

Prerequisites: `coq` (Rocq 9.1+)

```bash
make clean
make
```
