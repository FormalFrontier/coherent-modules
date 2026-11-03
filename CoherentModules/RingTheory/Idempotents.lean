/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Idempotents

/-!
# Finite coarsening of complete orthogonal idempotents

Summing a finite complete orthogonal family over the fibres of a map gives a complete
orthogonal family indexed by the target. The map need not be surjective: unused labels
have zero idempotent. The semiring need not be commutative, and empty index types and
zero semirings are allowed.

The proof uses Mathlib's characterization by ordered orthogonality products and total
sum, together with its fibrewise finite-sum identity.
-/

@[expose] public section

universe uA uI uJ

open scoped BigOperators

namespace CompleteOrthogonalIdempotents

variable {A : Type uA} [Semiring A]
variable {I : Type uI} {J : Type uJ} [Fintype I] [Fintype J] [DecidableEq J]
variable {P : I → A}

/-- Grouping a finite complete orthogonal family by the fibres of an arbitrary map
preserves completeness and orthogonality. Empty fibres contribute zero. -/
theorem sum_fiberwise (hP : CompleteOrthogonalIdempotents P) (q : I → J) :
    CompleteOrthogonalIdempotents (fun j ↦ ∑ i with q i = j, P i) := by
  refine iff_ortho_complete.mpr ⟨?_, ?_⟩
  · intro j k hjk
    rw [Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun i hi ↦ Finset.sum_eq_zero fun l hl ↦ ?_
    apply hP.ortho
    intro hil
    subst l
    exact hjk ((Finset.mem_filter.mp hi).2.symm.trans (Finset.mem_filter.mp hl).2)
  · rw [Finset.sum_fiberwise]
    exact hP.complete

end CompleteOrthogonalIdempotents
