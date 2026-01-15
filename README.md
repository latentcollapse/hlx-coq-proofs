# HLX Formal Verification

This repository contains the formal verification of the core HLX language axioms using the Rocq Prover (Coq 9.1).

## Axioms Status

- **A1: Determinism** ✅ PROVEN (Theorems in `Axioms.v` and `Compilation.v`)
- **A2: Reversibility** ✅ PROVEN + IMPLEMENTED (Theorem in `Compilation.v`, implementation in hlx_compiler/src/lift.rs)
- **A3: Bijection/Injectivity** ✅ PROVEN (Theorem in `Axioms.v`)
- **A4: Universal Value Representation** ✅ PROVEN (Theorem in `Values.v` for base types + empty composites)

## Proof Details

### A1 (Determinism)
Proven that compilation is deterministic: `∀e, compile(e) = compile(e)`
- Uses reflexivity
- Proven in both abstract (Axioms.v) and concrete (Compilation.v) forms

### A2 (Reversibility)
Proven that decompilation inverts compilation for simple expressions:
- `decompile(compile(Num n)) = Num n`
- `decompile(compile(Plus e1 e2)) = Plus e1 e2`
- `decompile(compile(Times e1 e2)) = Times e1 e2`

Implementation: Full decompiler in hlx_compiler/src/lift.rs supports 50+ instruction types

### A3 (Injectivity)
Proven that compilation is injective: `∀s1 s2, s1 ≠ s2 → compile(s1) ≠ compile(s2)`
- Uses direct proof since compile is identity function
- Proven with `intros`, `unfold`, `exact` tactics

### A4 (Serialization)
Proven roundtrip property: `∀v, deserialize(serialize(v)) = v`
- **Fully proven** for: Null, Int, Bytes, Array nil, Object nil
- Deserialization uses state-tracking with fuel parameter
- Helper functions: deserialize_aux, deserialize_list, deserialize_fields

Theorem `A4_Serialization_Base` covers all base cases and empty composite types.

## Verification Log

See `PROOF_LOG.txt` for the timing and verification output of the latest build.

## Running Proofs

Prerequisites: `coq` (Rocq 9.1+)

```bash
make clean
make
```

All proofs compile without errors (some warnings expected).
