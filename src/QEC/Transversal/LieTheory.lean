/-
Copyright (c) 2025 LeanQEC contributors. All rights reserved.
Released under MIT license.
Authors: LeanQEC contributors
-/
import QEC.Transversal.Defs
import QEC.ErrorDetection.Local
import Mathlib

/-!
# Lie Group Theory for Eastin-Knill

Axiomatized results from Lie group theory needed for the Eastin-Knill theorem.
These are stated without proof to focus on the QEC-specific arguments.

## Axioms

The key axioms capture:
1. Topological properties of unitary groups (compactness, connectedness)
2. Cartan's theorem on closed subgroups
3. Structure of quotients by connected components
4. The crucial fact that connected components act trivially on local-error-detecting codes

## References

* Eastin & Knill (2009)
* Hall, "Lie Groups, Lie Algebras, and Representations" (2015)
-/

open Matrix Topology

variable {n : ℕ}

/-! ### Topological properties of unitary groups -/

/-- AXIOM: The unitary group U(d) is compact -/
axiom unitaryGroup_isCompact (d : ℕ) [NeZero d] :
  IsCompact (unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ))

/-- AXIOM: The unitary group U(d) is connected -/
axiom unitaryGroup_isConnected (d : ℕ) [NeZero d] :
  IsConnected (unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ))

/-- AXIOM: Product unitaries T = ⨂ᵢ U(2) form a compact Lie group -/
axiom productUnitaries_isCompact (n : ℕ) :
  IsCompact (ProductUnitaries n)

/-! ### Lie subgroup structure -/

/-- AXIOM (Cartan's theorem): A closed subgroup of a Lie group is a Lie subgroup.
    Placeholder to avoid committing to a specific topology API. -/
axiom closedSubgroup_isLieSubgroup : True

/-- AXIOM: The set of logical operators {U : (I-P)UP = 0} is closed -/
axiom logicalOps_isClosed (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) :
  IsClosed { U | IsLogical P U }

/-! ### Connected components and quotients -/

/-- AXIOM: The connected component of identity behaves as expected.
    Placeholder to avoid committing to a specific topology API. -/
axiom connectedComponent_normal : True

/-- AXIOM: The quotient by the connected component is discrete.
    Placeholder to avoid committing to a specific topology API. -/
axiom quotient_by_connectedComponent_discrete : True

/-- AXIOM: A discrete subset of a compact space is finite -/
axiom discrete_subset_compact_finite {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {S : Set X} (hdiscrete : DiscreteTopology S) :
  S.Finite

/-! ### The key technical lemma -/

/-- AXIOM: The crucial observation for Eastin-Knill.
    Placeholder statement to avoid committing to a specific topology API. -/
axiom connectedComponent_acts_trivially
    (P : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (hP : P * P = P)
    (hdet : DetectsLocalErrors P) : True

