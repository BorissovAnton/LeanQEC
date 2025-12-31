/-
Copyright (c) 2025 LeanQEC contributors. All rights reserved.
Released under MIT license.
Authors: LeanQEC contributors
-/
import QEC.Pauli.Matrix
import QuantumInfo.Finite.Qubit.Basic

/-!
# Compatibility with Lean-QuantumInfo

Bridge between our group-theoretic Pauli types and Lean-QuantumInfo's matrix-based gates.

## Main results

* `Pauli.X_eq_Qubit_X` : Our X equals Lean-QuantumInfo's Qubit.X
* `Pauli.Y_eq_Qubit_Y` : Our Y equals Lean-QuantumInfo's Qubit.Y
* `Pauli.Z_eq_Qubit_Z` : Our Z equals Lean-QuantumInfo's Qubit.Z
-/

namespace Pauli

open Qubit

/-- Our Pauli X matrix equals Lean-QuantumInfo's Qubit.X -/
theorem X_eq_Qubit_X : Pauli.X.toMatrix1 = Qubit.X.val := by
  sorry

/-- Our Pauli Y matrix equals Lean-QuantumInfo's Qubit.Y -/
theorem Y_eq_Qubit_Y : Pauli.Y.toMatrix1 = Qubit.Y.val := by
  sorry

/-- Our Pauli Z matrix equals Lean-QuantumInfo's Qubit.Z -/
theorem Z_eq_Qubit_Z : Pauli.Z.toMatrix1 = Qubit.Z.val := by
  sorry

/-- Convert single-qubit Pauli to unitary group element -/
noncomputable def toUnitary (p : Pauli 1) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨p.toMatrix1, by
    sorry -- toMatrix_mem_unitary specialized to n=1
  ⟩

end Pauli
