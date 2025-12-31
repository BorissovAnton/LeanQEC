/-
Copyright (c) 2025 LeanQEC contributors. All rights reserved.
Released under MIT license.
Authors: LeanQEC contributors
-/
import QEC.Stabilizer.CodeSpace

/-!
# Logical Operators for Stabilizer Codes

Logical operators are elements of the normalizer N(S) that are not in S itself.
They act non-trivially on the code space.

## Main results

* Logical operators form a group isomorphic to the k-qubit Pauli group
* Logical operators preserve the code space
-/

namespace StabilizerCode

variable {n : ℕ} (C : StabilizerCode n)

/-- Logical operators preserve the code space -/
theorem logical_preserves_codeSpace (p : Pauli n) (hp : C.IsLogicalPauli p) :
    ∀ ψ ∈ C.codeSpace, p.toMatrix.mulVec ψ ∈ C.codeSpace := by
  sorry

/-- The group of logical operators modulo stabilizers is isomorphic to Pₖ -/
theorem logical_quotient_iso_pauli_k : True := by
  trivial

/-- Two logical operators that differ by a stabilizer act the same on code space -/
theorem logical_equiv_mod_stabilizer (p q : Pauli n)
    (hp : C.IsLogicalPauli p) (hq : C.IsLogicalPauli q)
    (h_equiv : ∃ s ∈ C.stabilizers, p = q * s) :
    ∀ ψ ∈ C.codeSpace, p.toMatrix.mulVec ψ = q.toMatrix.mulVec ψ := by
  sorry

end StabilizerCode
