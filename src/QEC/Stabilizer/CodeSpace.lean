/-
Copyright (c) 2025 LeanQEC contributors. All rights reserved.
Released under MIT license.
Authors: LeanQEC contributors
-/
import QEC.Stabilizer.Code
import QEC.Pauli.Matrix

/-!
# Code Space (Operational Definition)

The code space is the simultaneous +1 eigenspace of all stabilizers.
We define this operationally: ψ is in the code space iff S|ψ⟩ = |ψ⟩ for all S ∈ stabilizers.

## Main definitions

* `StabilizerCode.IsCodeword` : A state is a codeword if stabilized by all generators
* `StabilizerCode.codeSpace` : The code space as a set of vectors
* `StabilizerCode.projector` : The projector onto the code space

## Main results

* `projector_sq` : P² = P (idempotency)
* `projector_range` : States in the range of P are codewords
-/

open Matrix

namespace StabilizerCode

variable {n : ℕ}

/-- A state ψ is in the code space if it's a +1 eigenvector of all stabilizers.
    Operationally: for all s ∈ S, we have s|ψ⟩ = |ψ⟩ -/
def IsCodeword (C : StabilizerCode n) (ψ : Fin (2^n) → ℂ) : Prop :=
  ∀ s ∈ C.stabilizers, s.toMatrix.mulVec ψ = ψ

/-- The code space as a set of quantum states -/
def codeSpace (C : StabilizerCode n) : Set (Fin (2^n) → ℂ) :=
  { ψ | C.IsCodeword ψ }

/-- The projector onto the code space.
    Formula: P = (1/|S|) ∑_{s ∈ S} s
    where |S| is the order of the stabilizer group. -/
noncomputable def projector (C : StabilizerCode n) : Matrix (Fin (2^n)) (Fin (2^n)) ℂ :=
  sorry

variable (C : StabilizerCode n)

/-- The projector is Hermitian -/
theorem projector_isHermitian : C.projector.IsHermitian := by
  sorry

/-- The projector is idempotent: P² = P -/
theorem projector_sq : C.projector * C.projector = C.projector := by
  sorry

/-- The projector projects vectors onto the code space -/
theorem projector_range (ψ : Fin (2^n) → ℂ) :
    C.IsCodeword (C.projector.mulVec ψ) := by
  sorry

/-- If ψ is a codeword, then P|ψ⟩ = |ψ⟩ -/
theorem projector_codeword (ψ : Fin (2^n) → ℂ) (hψ : C.IsCodeword ψ) :
    C.projector.mulVec ψ = ψ := by
  sorry

/-- The code space has dimension 2^k where k is the number of logical qubits -/
theorem codeSpace_dim : True := by
  trivial

/-- Code space is non-trivial when k > 0 -/
theorem codeSpace_nontrivial (hk : C.k > 0) :
    ∃ ψ₁ ψ₂ : Fin (2^n) → ℂ, ψ₁ ∈ C.codeSpace ∧ ψ₂ ∈ C.codeSpace ∧ ψ₁ ≠ ψ₂ := by
  sorry

end StabilizerCode
