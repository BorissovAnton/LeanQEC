/-
Copyright (c) 2025 LeanQEC contributors. All rights reserved.
Released under MIT license.
Authors: LeanQEC contributors
-/
import QEC.Pauli.Symplectic
import Mathlib

/-!
# Stabilizer Codes

A stabilizer code is defined by an abelian subgroup of the Pauli group
that does not contain -I.

## Main definitions

* `StabilizerCode n` : A stabilizer code on n physical qubits
* `StabilizerCode.k` : Number of logical qubits encoded
* `StabilizerCode.normalizer` : The normalizer N(S) of the stabilizer group
* `StabilizerCode.logicalOps` : Logical operators (elements of N(S) \ S)

## References

* Gottesman, "Stabilizer Codes and Quantum Error Correction" (1997)
-/

/-- A stabilizer code on n physical qubits.
    
    The code is defined by a stabilizer group S, which is an abelian subgroup
    of the n-qubit Pauli group that does not contain -I. -/
structure StabilizerCode (n : ℕ) where
  /-- The stabilizer group S ⊆ Pₙ -/
  stabilizers : Subgroup (Pauli n)
  /-- S is abelian (all elements commute) -/
  isAbelian : ∀ s ∈ stabilizers, ∀ t ∈ stabilizers, Commute s t
  /-- -I ∉ S. We encode this as: if an element has phase 2 (representing -1),
      then it must have non-trivial X or Z parts. -/
  no_negI : ∀ s ∈ stabilizers, s.phase = 2 → (s.xBits ≠ BinVec.zero ∨ s.zBits ≠ BinVec.zero)

namespace StabilizerCode

variable {n : ℕ}

/-- Number of independent stabilizer generators.
    This would be computed as the rank of the stabilizer group. -/
noncomputable def numGenerators (C : StabilizerCode n) : ℕ := sorry

/-- Number of encoded logical qubits: k = n - rank(S) -/
noncomputable def k (C : StabilizerCode n) : ℕ := n - numGenerators C

/-- The normalizer N(S) = {P ∈ Pₙ | PSP⁻¹ = S}.
    Elements of N(S) either commute with all stabilizers (and thus preserve the code space)
    or anticommute with some stabilizers (and thus map between orthogonal code spaces). -/
def normalizer (C : StabilizerCode n) : Subgroup (Pauli n) :=
  C.stabilizers.normalizer

/-- An element is a logical Pauli if it's in N(S) but not in S -/
def IsLogicalPauli (C : StabilizerCode n) (p : Pauli n) : Prop :=
  p ∈ C.normalizer ∧ p ∉ C.stabilizers

/-- The set of logical Pauli operators -/
def logicalOps (C : StabilizerCode n) : Set (Pauli n) :=
  { p | C.IsLogicalPauli p }

/-- Code distance (minimum weight of logical operators).
    The weight of a Pauli is the number of qubits on which it acts non-trivially. -/
noncomputable def distance (C : StabilizerCode n) : ℕ := sorry

variable (C : StabilizerCode n)

/-- Elements of the normalizer preserve the code space -/
theorem normalizer_preserves_codeSpace (p : Pauli n) (hp : p ∈ C.normalizer) :
    ∀ s ∈ C.stabilizers, ∃ s' ∈ C.stabilizers, p * s * p⁻¹ = s' := by
  intro s hs
  -- This follows from the definition of normalizer
  sorry

/-- Logical operators commute with all stabilizers -/
theorem logical_commutes_with_stabilizers (p : Pauli n) (hp : C.IsLogicalPauli p) :
    ∀ s ∈ C.stabilizers, Commute p s := by
  intro s hs
  -- Elements of N(S) \ S that don't anticommute with any stabilizer must commute with all
  sorry

end StabilizerCode
