/-
Copyright (c) 2025 LeanQEC contributors. All rights reserved.
Released under MIT license.
Authors: LeanQEC contributors
-/
import QEC.Stabilizer.CodeSpace
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Local Error Detection

A code detects local errors if any single-site error E satisfies PEP ∝ P.

## Main definitions

* `singleSiteError` : An error acting on a single qubit
* `DetectsLocalErrors` : Property that a projector detects local errors

## Main results

* For stabilizer codes with distance ≥ 2, local errors are detected
-/

open Matrix

/-- An error operator acting on site j (acts as E on qubit j, identity elsewhere).
    This represents E ⊗ I ⊗ ... ⊗ I with E at position j. -/
noncomputable def singleSiteError (n : ℕ) (j : Fin n) (E : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin (2^n)) (Fin (2^n)) ℂ :=
  sorry  -- Tensor product: I ⊗ ... ⊗ E ⊗ ... ⊗ I

/-- A code detects local errors if for any single-site error E,
    PEP is proportional to P (i.e., PEP = cP for some constant c).
    
    This means either:
    1. E moves states out of the code space (PEP = 0), or
    2. E acts as a scalar on the code space (PEP = cP for c ≠ 0) -/
def DetectsLocalErrors {n : ℕ} (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) : Prop :=
  ∀ (j : Fin n) (E : Matrix (Fin 2) (Fin 2) ℂ),
    ∃ c : ℂ, P * singleSiteError n j E * P = c • P

/-- For stabilizer codes, local error detection follows from distance ≥ 2.
    
    If the distance is at least 2, then any single-qubit Pauli error is either:
    - A stabilizer (detectable), or
    - Not in the normalizer (moves out of code space) -/
theorem stabilizerCode_detects_local {n : ℕ} (C : StabilizerCode n)
    (hdist : C.distance ≥ 2) :
    DetectsLocalErrors C.projector := by
  sorry

/-- Alternative characterization: local Hermitian operators act proportionally.
    
    It suffices to check Hermitian operators since any operator can be decomposed
    into Hermitian parts. -/
theorem detectsLocalErrors_iff_hermitian {n : ℕ} (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) :
    DetectsLocalErrors P ↔
      ∀ (j : Fin n) (H : Matrix (Fin 2) (Fin 2) ℂ), H.IsHermitian →
        ∃ c : ℂ, P * singleSiteError n j H * P = c • P := by
  sorry

/-- For Pauli errors specifically (the relevant case for stabilizer codes) -/
theorem stabilizerCode_detects_pauli_errors {n : ℕ} (C : StabilizerCode n)
    (hdist : C.distance ≥ 2) :
    ∀ (p : Pauli 1), ∀ (j : Fin n),
      ∃ c : ℂ, C.projector * singleSiteError n j p.toMatrix1 * C.projector = c • C.projector := by
  sorry

