/-
Copyright (c) 2025 LeanQEC contributors. All rights reserved.
Released under MIT license.
Authors: LeanQEC contributors
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Data.Complex.Basic

/-!
# Product and Transversal Operators

Definitions of product operators (tensor products of single-qubit unitaries)
and transversal operators (products with respect to a partition).

## Main definitions

* `ProductUnitaries n` : Set of unitary product operators on n qubits
* `IsLogical` : An operator is logical if it preserves the code space
* `LogicalProductOps` : The set of logical product operators

## References

* Eastin & Knill, "Restrictions on Transversal Encoded Quantum Gate Sets" (2009)
-/

open Matrix

/-- The set of unitary product operators on n qubits:
    T = { U₁ ⊗ U₂ ⊗ ... ⊗ Uₙ | Uⱼ ∈ U(2) }
    
    These are the operators that act as a tensor product of single-qubit unitaries. -/
def ProductUnitaries (n : ℕ) : Set (Matrix (Fin (2^n)) (Fin (2^n)) ℂ) :=
  sorry  -- { U | ∃ (ops : Fin n → unitaryGroup (Fin 2) ℂ), U = ⨂ᵢ ops i }

/-- Product unitaries form a subgroup of U(2^n).
    Placeholder statement to be refined once subgroup APIs are finalized. -/
theorem productUnitaries_subgroup (n : ℕ) : True := by
  trivial

/-- An operator U is logical for code with projector P if it preserves the code space.
    Equivalently: (I - P)UP = 0, or PUP = UP -/
def IsLogical {n : ℕ} (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (U : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) : Prop :=
  (1 - P) * U * P = 0

/-- Equivalent characterization: PUP = UP -/
theorem isLogical_iff_preserves {n : ℕ} (P U : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (hP : P * P = P) :
    IsLogical P U ↔ P * U * P = U * P := by
  sorry

/-- The set of logical product operators for a code with projector P -/
def LogicalProductOps {n : ℕ} (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) :
    Set (Matrix (Fin (2^n)) (Fin (2^n)) ℂ) :=
  ProductUnitaries n ∩ { U | IsLogical P U }

/-- Logical product operators form a group.
    Placeholder statement to be refined once subgroup APIs are finalized. -/
theorem logicalProductOps_isGroup {n : ℕ} (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (hP : P * P = P) : True := by
  trivial
