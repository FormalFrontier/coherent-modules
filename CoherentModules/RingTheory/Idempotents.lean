/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.Idempotents

/-!
# Orthogonal idempotents, coarsening, and additive intertwining

For a finite family of additive endomorphisms whose sum is the identity, an additive map
intertwines it with an orthogonal idempotent family exactly when it maps each source range
into the corresponding target range. The source family need not be orthogonal, and the
target family need not be complete. The additive monoids need neither inverses nor
cancellation, and their universes are independent of each other and of the index universe.

Summing a finite complete orthogonal family over the fibres of a map gives a complete
orthogonal family indexed by the target. The map need not be surjective: unused labels
have zero idempotent. The semiring need not be commutative, and empty index types and
zero semirings are allowed.

## References

The range-action lemma generalizes the linear range calculation used in
`CompleteOrthogonalIdempotents.linearEquivPiRange`. Orthogonality and completeness use
Mathlib's `Mathlib.RingTheory.Idempotents` API. Intertwining uses Mathlib's additive
endomorphisms, semiconjugacy, and evaluation of finite sums; finite coarsening uses
Mathlib's fibrewise finite-sum identity.
-/

@[expose] public section

universe uA uI uJ uM uN

open scoped BigOperators

namespace OrthogonalIdempotents

variable {M : Type uM} [AddCommMonoid M]
variable {I : Type uI} {P : I → AddMonoid.End M}

/-- An orthogonal idempotent fixes every element of its own range and annihilates every
element of another member's range. -/
theorem apply_eq_ite_of_mem_range [DecidableEq I] (hP : OrthogonalIdempotents P)
    (i j : I) {x : M} (hx : x ∈ Set.range (P i)) :
    P j x = if j = i then x else 0 := by
  obtain ⟨y, rfl⟩ := hx
  change (P j * P i) y = if j = i then P i y else 0
  rw [hP.mul_eq]
  split_ifs with h
  · subst j
    rfl
  · rfl

variable {N : Type uN} [AddCommMonoid N] {Q : I → AddMonoid.End N}

/-- An additive map intertwines a finite family summing to the identity with an orthogonal
idempotent family if and only if it maps corresponding ranges into one another. Neither
source orthogonality nor target completeness is required. -/
theorem semiconj_iff_mapsTo_range [Fintype I] (hQ : OrthogonalIdempotents Q)
    (hsum : ∑ i, P i = 1) (h : M →+ N) :
    (∀ i, Function.Semiconj h (P i) (Q i)) ↔
      ∀ i, Set.MapsTo h (Set.range (P i)) (Set.range (Q i)) := by
  constructor
  · intro hh i x hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨h y, (hh i y).symm⟩
  · intro hh i x
    classical
    have hsum_apply : ∑ j, P j x = x := by
      have heval : (∑ j, P j) x = ∑ j, P j x :=
        AddMonoidHom.finsetSum_apply P Finset.univ x
      rw [hsum] at heval
      exact heval.symm
    symm
    calc
      Q i (h x) = Q i (h (∑ j, P j x)) := by rw [hsum_apply]
      _ = ∑ j, Q i (h (P j x)) := by simp only [map_sum]
      _ = ∑ j, if i = j then h (P j x) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        exact hQ.apply_eq_ite_of_mem_range j i (hh j ⟨x, rfl⟩)
      _ = h (P i x) := by simp

end OrthogonalIdempotents

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
