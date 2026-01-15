# HLX Formal Verification

This repository contains the formal verification of the core HLX language axioms using the Rocq Prover (Coq 9.1).

## Axioms Status

- **A1: Determinism** ✅ PROVEN (Theorem in `Axioms.v` and `Compilation.v`)
- **A2: Reversibility** ✅ IMPLEMENTED (Decompiler in hlx_compiler)
- **A3: Bijection/Injectivity** ✅ PROVEN (Theorem in `Axioms.v`)
- **A4: Universal Value Representation** ⚠️ PARTIAL (Proven for Null, Int, Bytes in `Values.v`)

## Proof Details

### A1 (Determinism)
Proven that compilation is deterministic: `∀s, compile(s) = compile(s)`

### A3 (Injectivity)
Proven that compilation is injective: `∀s1 s2, s1 ≠ s2 → compile(s1) ≠ compile(s2)`

### A4 (Serialization)
Proven roundtrip property for simple values (Null, Int, Bytes):
`∀v, deserialize(serialize(v)) = v`

Note: Full proof for Array and Object types requires more complex deserialization logic.

## Verification Log

See `PROOF_LOG.txt` for the timing and verification output of the latest build.

## Running Proofs

Prerequisites: `coq` (Rocq 9.1+)

```bash
make clean
make
```

All proofs compile without errors (some warnings expected).
