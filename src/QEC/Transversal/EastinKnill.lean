/-
Copyright (c) 2025 LeanQEC contributors. All rights reserved.
Released under MIT license.
Authors: LeanQEC contributors
-/
import QEC.Transversal.LieTheory
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Data.Complex.Basic

/-!
# The Eastin-Knill Theorem

For any nontrivial local-error-detecting quantum code,
the set of transversal logical unitary operators is not universal.

## Main results

* `eastin_knill` : The main theorem
* `eastin_knill_stabilizer` : Corollary for stabilizer codes

## References

* Eastin, B. & Knill, E. "Restrictions on Transversal Encoded Quantum Gate Sets",
  Physical Review Letters 102, 110502 (2009)
-/

open Matrix

variable {n : ℕ}

/-- A set of operators is universal if it can approximate any unitary operator
    on the code space to arbitrary precision.
    
    Placeholder definition to avoid committing to a specific operator norm. -/
def IsUniversal {d : ℕ} (S : Set (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  True

/-- The code space dimension (trace of the projector) -/
noncomputable def codeDim {n : ℕ} (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) : ℕ :=
  sorry  -- P.trace.re.toNat or similar

/-- A code is nontrivial if it encodes at least one logical qubit (dimension > 1) -/
def IsNontrivialCode {n : ℕ} (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) : Prop :=
  codeDim P > 1

/-- The set of logical operators induced on the code space.
    These are the effective operators acting on the k-dimensional code space. -/
noncomputable def InducedLogicalOps {n : ℕ} (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) :
    Set (Matrix (Fin (codeDim P)) (Fin (codeDim P)) ℂ) :=
  sorry  -- Restriction of LogicalProductOps P to the code space

/-!
## The Eastin-Knill Theorem

This is the main result: no local-error-detecting code can have universal transversal gates.
-/

/--
**Theorem (Eastin-Knill, 2009):**

For any nontrivial local-error-detecting quantum code,
the set of logical unitary product operators is not universal.

**Proof outline:**

1. Let G = LogicalProductOps(P) be the logical product operators
2. Let T = ProductUnitaries(n) be all product operators
3. G is a closed subgroup of the compact group T (Lie subgroup by Cartan)
4. Let C₀ be the connected component of the identity in G
5. The quotient Q = G/C₀ is discrete (and thus finite, being discrete in compact)
6. For local-error-detecting codes, C₀ acts trivially: ∀U ∈ C₀, UP = P
7. Therefore, distinct logical actions come only from elements of Q
8. Q is finite, so the induced logical operators form a finite set
9. A finite set cannot be universal for the infinite unitary group U(k)
10. Therefore G is not universal ∎

**Significance:**

This theorem explains why fault-tolerant quantum computation requires
non-transversal operations (measurements, magic state distillation, etc.).
It's a fundamental no-go result in quantum error correction.
-/
theorem eastin_knill
    (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (hproj : P * P = P)
    (hdet : DetectsLocalErrors P)
    (hnontrivial : IsNontrivialCode P) :
    ¬ IsUniversal (InducedLogicalOps P) := by
  sorry

/--
**Corollary:** For any nontrivial stabilizer code with distance ≥ 2,
transversal gates cannot be universal.

This is the formulation most relevant to quantum error correction practice.
-/
theorem eastin_knill_stabilizer (C : StabilizerCode n)
    (hdist : C.distance ≥ 2)
    (hk : C.k > 0) :
    ¬ IsUniversal (InducedLogicalOps C.projector) := by
  sorry

/-
Historical note:

This theorem was conjectured for many years before Eastin and Knill's proof.
Earlier partial results had shown non-universality for specific code families:

- Zeng et al. (2007): Proved for qubit stabilizer codes
- Chen et al. (2008): Extended to qudit stabilizer codes

Eastin and Knill's contribution was to prove the result for all local-error-detecting
codes using Lie group theory, not just stabilizer codes.
-/

