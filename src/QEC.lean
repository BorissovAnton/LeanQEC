/-
Copyright (c) 2025 LeanQEC contributors. All rights reserved.
Released under MIT license.
Authors: LeanQEC contributors
-/

-- Pauli group infrastructure
import QEC.Pauli.Defs
import QEC.Pauli.Matrix
import QEC.Pauli.Symplectic
import QEC.Pauli.Compat

-- Stabilizer codes
import QEC.Stabilizer.Code
import QEC.Stabilizer.CodeSpace
import QEC.Stabilizer.Logical

-- Error detection
import QEC.ErrorDetection.Local

-- Transversal gates and Eastin-Knill theorem
import QEC.Transversal.Defs
import QEC.Transversal.LieTheory
import QEC.Transversal.EastinKnill

-- Example codes
import QEC.Codes.Steane

/-!
# LeanQEC: Quantum Error Correction in Lean 4

This library provides formalized definitions and theorems for quantum error correction,
with a focus on stabilizer codes and the Eastin-Knill theorem.

## Main Components

### Pauli Group (`QEC.Pauli`)
- **`Pauli n`**: The n-qubit Pauli group with phase tracking (Gottesman conventions)
- **`symplecticInner`**: Symplectic inner product determining commutation relations
- **`toMatrix`**: Conversion to unitary matrices
- Compatibility layer with Lean-QuantumInfo

### Stabilizer Codes (`QEC.Stabilizer`)
- **`StabilizerCode n`**: Codes defined by abelian subgroups of the Pauli group
- **`IsCodeword`**: Operational definition of code space
- **`logicalOps`**: Logical Pauli operators (normalizer quotient)

### Eastin-Knill Theorem (`QEC.Transversal`)
- **`eastin_knill`**: Main theorem - transversal gates cannot be universal
  for local-error-detecting codes
- **`ProductUnitaries`**: Definition of product operators
- **Axiomatized Lie theory**: Key mathematical infrastructure

### Example: Steane Code (`QEC.Codes`)
- **`Steane.code`**: The [[7,1,3]] Steane code
- **`Steane.logicalX`, `Steane.logicalZ`**: Logical operators

## Key Theorems

### Pauli Group
```lean
theorem commute_iff_symplectic_zero (p q : Pauli n) :
    Commute p q ↔ symplecticInner p q = 0
```

### Eastin-Knill
```lean
theorem eastin_knill {n : ℕ}
    (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (hproj : P * P = P)
    (hdet : DetectsLocalErrors P)
    (hnontrivial : IsNontrivialCode P) :
    ¬ IsUniversal (InducedLogicalOps P)
```

## References

1. **Gottesman, D.** "Stabilizer Codes and Quantum Error Correction"
   PhD Thesis, Caltech (1997). [quant-ph/9705052]

2. **Eastin, B. & Knill, E.** "Restrictions on Transversal Encoded Quantum Gate Sets"
   Physical Review Letters 102, 110502 (2009).

3. **Steane, A.** "Error Correcting Codes in Quantum Theory"
   Physical Review Letters 77, 793 (1996).

## Design Philosophy

This library prioritizes:
- **Clean theorem statements** over complete proofs
- **Operational definitions** (e.g., code space as eigenvectors) over abstract ones
- **Axiomatized Lie theory** to focus on QEC-specific arguments
- **Compatibility** with the Lean-QuantumInfo ecosystem

Many theorems use `sorry` to maintain focus on the mathematical architecture.
Future work will fill in proofs and extend to CSS codes, fault tolerance, and LDPC codes.

## Dependencies

- Lean 4.24.0
- Mathlib4
- Lean-QuantumInfo (for quantum information foundations)
-/
