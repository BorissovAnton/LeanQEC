/-
Copyright (c) 2025 LeanQEC contributors. All rights reserved.
Released under MIT license.
Authors: LeanQEC contributors
-/
import QEC.Pauli.Defs
import Mathlib.Algebra.Group.Commutator

/-!
# Symplectic representation of the Pauli group

The symplectic inner product over F₂ determines commutation relations.

## Main definitions

* `symplecticInner` : Symplectic inner product ⟨(a,b), (a',b')⟩ = a·b' + a'·b mod 2

## Main results

* `commute_iff_symplectic_zero` : Two Paulis commute iff symplectic inner product is 0
* `anticommute_iff_symplectic_one` : Two Paulis anticommute iff symplectic inner product is 1
-/

namespace Pauli

variable {n : ℕ}

/-- Symplectic inner product on F₂^{2n}.
    For two Paulis p = (phase₁, a, b) and q = (phase₂, a', b'),
    the symplectic inner product is: ⟨p, q⟩ = a·b' + a'·b mod 2
    
    This determines commutation: p and q commute iff ⟨p, q⟩ = 0 -/
def symplecticInner (p q : Pauli n) : Fin 2 :=
  (BinVec.dot p.xBits q.zBits + BinVec.dot q.xBits p.zBits) % 2

/-- Symplectic inner product is symmetric -/
theorem symplecticInner_comm (p q : Pauli n) :
    symplecticInner p q = symplecticInner q p := by
  sorry

/-- Two Paulis commute iff their symplectic inner product is 0.
    
    This is the fundamental connection between the group-theoretic
    and symplectic representations of the Pauli group. -/
theorem commute_iff_symplectic_zero (p q : Pauli n) :
    Commute p q ↔ symplecticInner p q = 0 := by
  sorry

/-- Two Paulis anticommute iff their symplectic inner product is 1 -/
theorem anticommute_iff_symplectic_one (p q : Pauli n) :
    p * q * p⁻¹ * q⁻¹ = Pauli.mk 2 BinVec.zero BinVec.zero ↔ symplecticInner p q = 1 := by
  sorry

/-- If symplectic inner product is 0, the Paulis commute -/
theorem symplectic_zero_imp_commute (p q : Pauli n) (h : symplecticInner p q = 0) :
    Commute p q := by
  exact (commute_iff_symplectic_zero p q).mpr h

/-- X and Z anticommute on the same qubit -/
theorem X_Z_anticommute : symplecticInner X Z = 1 := by
  sorry

/-- X and X commute (same operator) -/
theorem X_X_commute : symplecticInner X X = 0 := by
  sorry

end Pauli
