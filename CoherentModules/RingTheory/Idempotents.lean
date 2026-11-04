/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Logic.Function.Conjugate
public import Mathlib.RingTheory.Idempotents

/-!
# Orthogonal idempotents, coarsening, and additive intertwining

For a finite family of additive endomorphisms whose sum is the identity, an additive map
intertwines it with an orthogonal idempotent family exactly when it maps each source range
into the corresponding target range. The source family need not be orthogonal, and the
target family need not be complete. The additive commutative monoids need neither inverses
nor cancellation, and their universes are independent of each other and of the index universe.

Fibrewise intertwining allows a finite source index type `I`, an arbitrary target index
type `J` with decidable equality, and a map `q : I → J`. For an orthogonal idempotent
target family, mapping each source range into its `q`-labelled target range suffices to
intertwine each fibre-sum of source endomorphisms with the corresponding target endomorphism.
This requires only that the source sum be the identity, not source orthogonality; with a
complete orthogonal idempotent source family it is an equivalence. The target family need
not be complete, and `q` may merge or omit labels. Unused target endomorphisms need only
kill the image of the additive map, not vanish globally. The two monoid and two index
universes are independent, and no scalar compatibility is required.

In contrast, coarsening a finite complete orthogonal family by fibrewise sums packages a
complete orthogonal family when the target index type is also finite. The map need not
be surjective: unused labels have zero idempotent. The semiring need not be commutative,
and empty index types and zero semirings are allowed.

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

end OrthogonalIdempotents

section FiberwiseSemiconj

variable {M : Type uM} [AddCommMonoid M] {N : Type uN} [AddCommMonoid N]
variable {I : Type uI} {J : Type uJ} [Fintype I] [DecidableEq J]
variable {P : I → AddMonoid.End M} {Q : J → AddMonoid.End N}

/-- An additive map that sends each source range into the target range at its image label
intertwines each fibre sum with the corresponding target idempotent. The source family
need only sum to the identity; it need not be orthogonal. The target index type need not
be finite, and the target family need not be complete. Empty fibres contribute zero. -/
theorem OrthogonalIdempotents.semiconj_sum_fiberwise_of_mapsTo_range
    (hQ : OrthogonalIdempotents Q) (hsum : ∑ i, P i = 1)
    (q : I → J) (h : M →+ N)
    (hh : ∀ i, Set.MapsTo h (Set.range (P i)) (Set.range (Q (q i)))) :
    ∀ j, Function.Semiconj h (∑ i with q i = j, P i) (Q j) := by
  classical
  intro j x
  simp only [Finset.sum_apply]
  have hsum_apply : ∑ i, P i x = x := by
    have heval : (∑ i, P i) x = ∑ i, P i x :=
      AddMonoidHom.finsetSum_apply P Finset.univ x
    rw [hsum] at heval
    exact heval.symm
  symm
  calc
    Q j (h x) = Q j (h (∑ i, P i x)) := by rw [hsum_apply]
    _ = ∑ i, Q j (h (P i x)) := by simp only [map_sum]
    _ = ∑ i, if q i = j then h (P i x) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [eq_comm] using
        hQ.apply_eq_ite_of_mem_range (q i) j (hh i ⟨x, rfl⟩)
    _ = ∑ i with q i = j, h (P i x) := by rw [Finset.sum_filter]
    _ = h (∑ i with q i = j, P i x) := by rw [map_sum]

end FiberwiseSemiconj

namespace OrthogonalIdempotents

variable {M : Type uM} [AddCommMonoid M]
variable {I : Type uI} {P : I → AddMonoid.End M}
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
  · intro hh
    classical
    simpa only [id_eq, Finset.sum_filter, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] using
      hQ.semiconj_sum_fiberwise_of_mapsTo_range hsum id h hh

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

section FiberwiseSemiconj

variable {M : Type uM} [AddCommMonoid M] {N : Type uN} [AddCommMonoid N]
variable {I : Type uI} {J : Type uJ} [Fintype I] [DecidableEq J]
variable {P : I → AddMonoid.End M} {Q : J → AddMonoid.End N}

/-- An additive map intertwines the fibre sums of a complete orthogonal family with an
orthogonal target family if and only if it sends each fine source range into the target
range at its image label. The target index type need not be finite, and the target family
need not be complete. The label map may be noninjective or nonsurjective. -/
theorem CompleteOrthogonalIdempotents.semiconj_sum_fiberwise_iff_mapsTo_range
    (hP : CompleteOrthogonalIdempotents P) (hQ : OrthogonalIdempotents Q)
    (q : I → J) (h : M →+ N) :
    (∀ j, Function.Semiconj h (∑ i with q i = j, P i) (Q j)) ↔
      ∀ i, Set.MapsTo h (Set.range (P i)) (Set.range (Q (q i))) := by
  constructor
  · intro hh i y hy
    classical
    have hfix : (∑ k with q k = q i, (P k : M → M)) y = y := by
      calc
        (∑ k with q k = q i, (P k : M → M)) y = ∑ k with q k = q i, P k y :=
          Finset.sum_apply y _ _
        _ = ∑ k with q k = q i, if k = i then y else 0 := by
          apply Finset.sum_congr rfl
          intro k _
          exact hP.toOrthogonalIdempotents.apply_eq_ite_of_mem_range i k hy
        _ = y := by simp
    exact ⟨h y, (hh (q i) y).symm.trans (congrArg h hfix)⟩
  · exact hQ.semiconj_sum_fiberwise_of_mapsTo_range hP.complete q h

end FiberwiseSemiconj
