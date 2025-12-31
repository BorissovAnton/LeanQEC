# LeanQEC: Quantum Error Correction in Lean 4

A formal verification library for quantum error correction, focusing on stabilizer codes and the Eastin-Knill theorem.

## Features

- **Pauli Group Formalization**: n-qubit Pauli group with Gottesman phase conventions
- **Stabilizer Codes**: Operational definitions with code space and logical operators
- **Eastin-Knill Theorem**: Formalized statement that transversal gates cannot be universal for local-error-detecting codes
- **Steane Code**: The [[7,1,3]] code as a working example
- **Lean-QuantumInfo Integration**: Compatibility layer for seamless interoperation

## Project Structure

```
LeanQEC/
├── src/QEC/
│   ├── Pauli/              # Pauli group infrastructure
│   │   ├── Defs.lean       # Core definitions and group structure
│   │   ├── Matrix.lean     # Matrix representations
│   │   ├── Symplectic.lean # F₂ representation and commutation
│   │   └── Compat.lean     # Lean-QuantumInfo compatibility
│   ├── Stabilizer/         # Stabilizer code theory
│   │   ├── Code.lean       # StabilizerCode structure
│   │   ├── CodeSpace.lean  # Operational code space
│   │   └── Logical.lean    # Logical operators
│   ├── Transversal/        # Transversal gates
│   │   ├── Defs.lean       # Product operators
│   │   ├── LieTheory.lean  # Axiomatized Lie theory
│   │   └── EastinKnill.lean # Main theorem
│   ├── ErrorDetection/
│   │   └── Local.lean      # Local error detection
│   └── Codes/
│       └── Steane.lean     # Steane [[7,1,3]] code
├── QEC.lean                # Main entry point
├── lakefile.lean           # Build configuration
└── lean-toolchain          # Lean version
```

## Building

```bash
# Get dependencies
lake exe cache get

# Build the library
lake build
```

## Quick Start

```lean
import QEC

open Pauli

-- Single-qubit Pauli operators
#check Pauli.X
#check Pauli.Y
#check Pauli.Z

-- Tensor product
#check X ⊗ₚ Z  -- 2-qubit Pauli: X ⊗ Z

-- Symplectic inner product determines commutation
example : Commute X Z ↔ symplecticInner X Z = 0 := 
  commute_iff_symplectic_zero X Z

-- The Steane code
open Steane

#check Steane.code : StabilizerCode 7
#check steane_k : code.k = 1  -- Encodes 1 logical qubit
#check steane_distance : code.distance = 3  -- Distance 3

-- Eastin-Knill theorem
#check eastin_knill  -- Transversal gates cannot be universal
```

## Key Definitions

### Pauli Group

The n-qubit Pauli group is represented as:
```lean
structure Pauli (n : ℕ) where
  phase : ZMod 4        -- {1, i, -1, -i}
  xBits : BinVec n      -- X component
  zBits : BinVec n      -- Z component
```

Group multiplication follows Gottesman's formula:
```
(p₁, a₁, b₁) * (p₂, a₂, b₂) = (p₁ + p₂ + 2(b₁·a₂), a₁+a₂, b₁+b₂)
```

### Stabilizer Codes

```lean
structure StabilizerCode (n : ℕ) where
  stabilizers : Subgroup (Pauli n)
  isAbelian : ...
  no_negI : ...
```

Code space defined operationally:
```lean
def IsCodeword (ψ : Fin (2^n) → ℂ) : Prop :=
  ∀ s ∈ stabilizers, s.toMatrix.mulVec ψ = ψ
```

### Eastin-Knill Theorem

```lean
theorem eastin_knill
    (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (hproj : P * P = P)
    (hdet : DetectsLocalErrors P)
    (hnontrivial : IsNontrivialCode P) :
    ¬ IsUniversal (InducedLogicalOps P)
```

**Interpretation**: No nontrivial local-error-detecting code can have universal transversal gates.

## Implementation Status

✅ **Complete:**
- Pauli group with Gottesman conventions
- Stabilizer code definitions
- Eastin-Knill theorem statement
- Steane code example

🚧 **With `sorry` (mathematical infrastructure):**
- Group axioms for Pauli multiplication
- Lie group theory (axiomatized)
- Tensor product constructions
- Distance calculations

## References

1. **Gottesman, D.** (1997) "Stabilizer Codes and Quantum Error Correction"  
   PhD Thesis, Caltech. [quant-ph/9705052]

2. **Eastin, B. & Knill, E.** (2009) "Restrictions on Transversal Encoded Quantum Gate Sets"  
   Physical Review Letters 102, 110502.

3. **Steane, A.** (1996) "Error Correcting Codes in Quantum Theory"  
   Physical Review Letters 77, 793.

## Dependencies

- [Lean 4.24.0](https://leanprover.github.io/)
- [Mathlib4](https://github.com/leanprover-community/mathlib4)
- [Lean-QuantumInfo](https://github.com/Timeroot/Lean-QuantumInfo)

## Future Work

- Prove Pauli group axioms
- CSS construction (codes from classical codes)
- Standard form algorithm for stabilizer codes
- Additional codes: 5-qubit, surface code, toric code
- Fault-tolerant gate constructions
- Distance bounds (quantum Hamming, Singleton)

## Contributing

Contributions are welcome! Areas of interest:
- Filling in `sorry`s with complete proofs
- Adding more example codes
- Extending to LDPC and topological codes
- Connecting to fault tolerance theory

## License

MIT License. See [LICENSE](LICENSE) for details.

## Citation

```bibtex
@misc{leanqec2025,
  title = {LeanQEC: Quantum Error Correction in Lean 4},
  year = {2025},
  howpublished = {\url{https://github.com/yourusername/LeanQEC}},
}
```

## Acknowledgments

- Built on [Lean-QuantumInfo](https://github.com/Timeroot/Lean-QuantumInfo) by Alex Meiburg
- Inspired by Gottesman's foundational work on stabilizer codes
- Eastin-Knill theorem formalization based on their 2009 paper
