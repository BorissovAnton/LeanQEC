/-
Copyright (c) 2025 LeanQEC contributors. All rights reserved.
Released under MIT license.
Authors: LeanQEC contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Complex.Basic

/-!
# The n-qubit Pauli Group

Following Gottesman's conventions from quant-ph/9705052:
- Phases are {1, i, -1, -i} encoded as ZMod 4
- An n-qubit Pauli is (phase, X-component, Z-component)
- X-component and Z-component are bit vectors in (Fin n → Fin 2)

The group operation accounts for the phase from Y = iXZ and commutation.

## Main definitions

* `Phase` : The four phase values {1, i, -1, -i} as ZMod 4
* `BinVec n` : Binary vectors of length n
* `Pauli n` : The n-qubit Pauli group
* `Pauli.X`, `Pauli.Y`, `Pauli.Z` : Single-qubit Paulis
* `Pauli.tensor` : Tensor product of Paulis

## References

* Gottesman, "Stabilizer Codes and Quantum Error Correction" (1997)
-/

/-- Phase elements {1, i, -1, -i} as ZMod 4 where:
    0 ↦ 1, 1 ↦ i, 2 ↦ -1, 3 ↦ -i -/
abbrev Phase := ZMod 4

/-- Binary vector over n bits -/
abbrev BinVec (n : ℕ) := Fin n → Fin 2

namespace BinVec

variable {n : ℕ}

/-- Pointwise addition of binary vectors mod 2 -/
def add (a b : BinVec n) : BinVec n := fun i => (a i + b i) % 2

/-- Dot product of binary vectors mod 2 -/
def dot (a b : BinVec n) : Fin 2 :=
  Finset.univ.sum (fun i => a i * b i) % 2

/-- Zero vector -/
def zero : BinVec n := fun _ => 0

end BinVec

/-- The n-qubit Pauli group.
    Elements (phase, xBits, zBits) represent: i^phase · X^xBits · Z^zBits
    where X^xBits means X applied to positions where xBits = 1, etc. -/
structure Pauli (n : ℕ) where
  phase : Phase
  xBits : BinVec n
  zBits : BinVec n
  deriving DecidableEq, Repr

namespace Pauli

variable {n m : ℕ}

/-- Pauli group multiplication.
    The phase picks up contributions from:
    1. Individual phases p₁ + p₂
    2. Y = iXZ contributes phase when X and Z overlap
    3. Commutation: XZ = -ZX contributes phase when operators don't commute
    
    Formula: (p₁, a₁, b₁) * (p₂, a₂, b₂) = (p₁ + p₂ + 2(b₁·a₂), a₁+a₂, b₁+b₂)
    where the 2(b₁·a₂) term accounts for commutation phases -/
def mul (p q : Pauli n) : Pauli n where
  phase := p.phase + q.phase + 2 * BinVec.dot p.zBits q.xBits
  xBits := BinVec.add p.xBits q.xBits
  zBits := BinVec.add p.zBits q.zBits

/-- Identity element: I⊗...⊗I with phase 1 -/
def one : Pauli n where
  phase := 0
  xBits := BinVec.zero
  zBits := BinVec.zero

/-- Inverse of a Pauli element.
    Since X² = Z² = I, the X and Z parts are self-inverse.
    The phase must be adjusted to cancel: p · p⁻¹ = 1 -/
def inv (p : Pauli n) : Pauli n where
  phase := (-(p.phase + 2 * BinVec.dot p.xBits p.zBits : ZMod 4))
  xBits := p.xBits
  zBits := p.zBits

instance : Mul (Pauli n) := ⟨mul⟩
instance : One (Pauli n) := ⟨one⟩
instance : Inv (Pauli n) := ⟨inv⟩

/-- The n-qubit Pauli group structure -/
instance : Group (Pauli n) where
  mul_assoc := by
    intro a b c
    sorry
  one_mul := by
    intro a
    sorry
  mul_one := by
    intro a
    sorry
  inv_mul_cancel := by
    intro a
    sorry

/-- Single-qubit Pauli I (identity) -/
def I : Pauli 1 := one

/-- Single-qubit Pauli X -/
def X : Pauli 1 where
  phase := 0
  xBits := ![1]
  zBits := ![0]

/-- Single-qubit Pauli Y = iXZ -/
def Y : Pauli 1 where
  phase := 1  -- phase i
  xBits := ![1]
  zBits := ![1]

/-- Single-qubit Pauli Z -/
def Z : Pauli 1 where
  phase := 0
  xBits := ![0]
  zBits := ![1]

/-- Tensor product of Paulis.
    (p₁ ⊗ p₂) has phase p₁.phase + p₂.phase and concatenated bit strings. -/
def tensor (p : Pauli m) (q : Pauli n) : Pauli (m + n) where
  phase := p.phase + q.phase
  xBits := Fin.append p.xBits q.xBits
  zBits := Fin.append p.zBits q.zBits

infixl:70 " ⊗ₚ " => tensor

/-- X² = I -/
theorem X_sq : X * X = (I : Pauli 1) := by
  sorry

/-- Y² = I (up to global phase -1) -/
theorem Y_sq : Y * Y = Pauli.mk 2 ![0] ![0] := by
  sorry

/-- Z² = I -/
theorem Z_sq : Z * Z = (I : Pauli 1) := by
  sorry

end Pauli
