/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Formal Frontier AI agents

The finite-free reindexing and scalar-tower transitivity arguments are adapted from Mathlib:
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import CoherentModules.Basic
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite presentation and coherence

This file constructs finite-free exact data for finitely presented semimodules
over semirings. Over rings, finite presentation is transitive along scalar towers
and descends from the base ring when the scalar ring is module-finite, for additive
commutative monoids with their given compatible actions. A finitely presented
module over a scalar ring that is coherent over the base ring is coherent for
its given compatible base action.
The fixed-ring specialization identifies finite presentation with coherence over
a coherent ring and deduces finite presentation of kernels between them. The
scalar and module universes are independent. It also gives a five-term
exact-sequence criterion for finite presentation of the middle module.

## Main declarations

* `Module.FinitePresentation.exists_fin_exact`: a finitely presented semimodule
  over a semiring admits finite-free maps forming an exact pair, with the map
  to the semimodule surjective.
* `Module.FinitePresentation.trans_of_tower`: finite presentation is transitive
  along scalar towers of possibly noncommutative rings.
* `Module.FinitePresentation.of_restrictScalars`: finite presentation descends
  from the base ring when the scalar ring is finite over it.
* `Module.FinitePresentation.restrictScalars_iff`: finite presentation over either
  ring is equivalent when the scalar ring is finitely presented over the base.
* `Module.FinitePresentation.trans_of_algebra`: the commutative-algebra
  specialization of scalar-tower transitivity, with Mathlib's argument order.
* `Module.FinitePresentation.isCoherent_restrictScalars`: a finitely presented
  module over a scalar ring coherent over the base ring is coherent over the base.
* `Module.isCoherent_restrictScalars_iff`: coherence over the base and scalar rings
  is equivalent when the scalar ring is coherent over the base.
* `Module.isCoherent_restrictScalars_iff_finitePresentation`: coherence over the
  base is equivalent to finite presentation over a scalar ring coherent over it.
* `Module.FinitePresentation.isCoherent`: the fixed-ring specialization over a
  coherent ring.
* `Module.isCoherent_iff_finitePresentation`: coherence is equivalent to finite
  presentation over a coherent ring.
* `Module.FinitePresentation.ker`: the kernel of a map between finitely
  presented modules over a coherent ring is finitely presented.
* `Module.FinitePresentation.of_exact_five`: in a sequence of five modules
  exact at the middle three, suitable finiteness hypotheses on the other four
  imply finite presentation of the middle module.

## Implementation notes

Over semirings, `Module.FinitePresentation` controls a finitely generated zero
fiber, not all pairs with equal image. Accordingly, `Function.Exact` in the
finite-free result means that the zero fiber is the range of the preceding
map; no congruence presentation or cokernel universal property is asserted.

The finite-presentation scalar-tower results retain the given actions on the
scalar ring and target, in three independent universes. Additive inverses on
the target are derived only inside the proofs, with the same additive-monoid
structure. No coherence or Noetherian hypothesis is used for these results.

## References

The finite-free construction follows the Mathlib contributors' formalizations
of finite presentation, finite generation, finite reindexing and exactness,
including Andrew Yang's `Module.FinitePresentation.exists_fin`. The scalar-tower
transitivity theorem generalizes Andrew Yang's Mathlib
`Module.FinitePresentation.trans`; its commutative-algebra specialization follows
from the general theorem. These finite-presentation proofs reuse Mathlib's
fixed-ring finite-product presentations, finite-free surjections, finite
generation under scalar restriction, and kernel and quotient criteria. The coherence
results use Mathlib's compatible scalar actions, finite images and first-isomorphism
equivalence, together with the coherent-module finite-product and quotient APIs.
-/

@[expose] public section

universe u v w v1 v2 v3 v4 v5

namespace Module

section Semiring

variable (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M]

/-- A finitely presented semimodule admits a surjective map from a finite free
semimodule whose zero fiber is the range of a map from a finite free semimodule.

Over semirings, `Function.Exact` records only zero-fiber exactness, not a
congruence presentation or a cokernel universal property. This generalizes
Mathlib's `Module.FinitePresentation.exists_fin'`. -/
theorem FinitePresentation.exists_fin_exact [Module.FinitePresentation R M] :
    ∃ (n m : ℕ) (g : (Fin n → R) →ₗ[R] M)
      (f : (Fin m → R) →ₗ[R] (Fin n → R)),
      Function.Surjective g ∧ Function.Exact f g := by
  classical
  obtain ⟨s, hs, hK⟩ := Module.FinitePresentation.out (R := R) (M := M)
  let p : (s →₀ R) →ₗ[R] M := Finsupp.linearCombination R ((↑) : s → M)
  let e : (s →₀ R) ≃ₗ[R] (Fin s.card → R) :=
    Finsupp.lcongr s.equivFin (LinearEquiv.refl R R) ≪≫ₗ
      Finsupp.linearEquivFunOnFinite R R (Fin s.card)
  obtain ⟨m, h, hh⟩ :=
    (Submodule.fg_iff_exists_fin_linearMap R (s →₀ R) (N := LinearMap.ker p)).mp hK
  have hp : Function.Surjective p := by
    apply LinearMap.range_eq_top.mp
    simpa [p, Finsupp.range_linearCombination] using hs
  refine ⟨s.card, m, p ∘ₗ e.symm.toLinearMap, e.toLinearMap ∘ₗ h, ?_, ?_⟩
  · exact hp.comp e.symm.surjective
  · exact (LinearEquiv.conj_exact_iff_exact h p e).mpr
      (LinearMap.exact_iff.mpr hh.symm)

end Semiring

section ScalarTower

variable (R : Type u) (S : Type v) (N : Type w)
variable [Ring R] [Ring S] [AddCommMonoid N]
variable [Module R S] [Module R N] [Module S N]
variable [IsScalarTower R S S] [IsScalarTower R S N]

/-- Finite presentation is transitive along a scalar tower of rings, using the
supplied module structures on the scalar ring and target.

This generalizes Andrew Yang's Mathlib `Module.FinitePresentation.trans` to
possibly noncommutative rings and an additive commutative monoid target. -/
theorem FinitePresentation.trans_of_tower
    [Module.FinitePresentation R S] [Module.FinitePresentation S N] :
    Module.FinitePresentation R N := by
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup R (M := N)
  obtain ⟨n, K, e, hK⟩ := Module.FinitePresentation.exists_fin S N
  let q : (Fin n → S) →ₗ[S] N := e.symm.toLinearMap ∘ₗ K.mkQ
  let qR : (Fin n → S) →ₗ[R] N := q.restrictScalars R
  let _ : Module.FinitePresentation R (Fin n → S) :=
    Module.FinitePresentation.pi (fun _ : Fin n => S)
  have hq : Function.Surjective q := e.symm.surjective.comp K.mkQ_surjective
  have hker : (LinearMap.ker q).FG := by
    simpa [q] using hK
  refine Module.finitePresentation_of_surjective qR hq ?_
  simpa only [qR, LinearMap.ker_restrictScalars] using hker.restrictScalars (R := R)

/-- Finite presentation over the base ring descends to the scalar ring when the
latter is finite as a module over the base. Both rings may be noncommutative,
and the target retains its given additive-monoid structure and scalar actions.

Scalar finiteness makes the finite-free scalar cover finite over the base, so
Mathlib's finite-presentation kernel criterion applies to its surjection. -/
theorem FinitePresentation.of_restrictScalars
    [Module.Finite R S] [Module.FinitePresentation R N] :
    Module.FinitePresentation S N := by
  let _ : AddCommGroup N := Module.addCommMonoidToAddCommGroup R (M := N)
  let _ : Module.Finite S N := Module.Finite.of_restrictScalars_finite R S N
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' S N
  let gR : (Fin n → S) →ₗ[R] N := g.restrictScalars R
  let _ : Module.Finite R (Fin n → S) := Module.Finite.pi
  have hgR : Function.Surjective gR := hg
  have hkerR : ((LinearMap.ker g).restrictScalars R).FG := by
    simpa only [gR, LinearMap.ker_restrictScalars] using
      Module.FinitePresentation.fg_ker gR hgR
  exact Module.finitePresentation_of_free_of_surjective g hg
    (Submodule.FG.of_restrictScalars R hkerR)

/-- If the scalar ring is finitely presented over the base, finite presentation
over either ring is equivalent for the given compatible actions. -/
theorem FinitePresentation.restrictScalars_iff [Module.FinitePresentation R S] :
    Module.FinitePresentation R N ↔ Module.FinitePresentation S N := by
  constructor
  · intro h
    let _ : Module.FinitePresentation R N := h
    exact Module.FinitePresentation.of_restrictScalars R S N
  · intro h
    let _ : Module.FinitePresentation S N := h
    exact Module.FinitePresentation.trans_of_tower R S N

end ScalarTower

/-- The commutative-algebra specialization of finite-presentation transitivity,
with the type and argument order of Andrew Yang's Mathlib
`Module.FinitePresentation.trans`, proved by scalar-tower transitivity. -/
theorem FinitePresentation.trans_of_algebra
    (R : Type u) (N : Type w) [CommRing R] [AddCommGroup N] [Module R N]
    (S : Type v) [CommRing S] [Algebra R S]
    [Module S N] [IsScalarTower R S N]
    [Module.FinitePresentation R S] [Module.FinitePresentation S N] :
    Module.FinitePresentation R N :=
  Module.FinitePresentation.trans_of_tower R S N

section Ring

private theorem FinitePresentation.exists_fin'_ring
    (R : Type u) (M : Type v) [Ring R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] :
    ∃ (n m : ℕ) (f : (Fin n → R) →ₗ[R] M)
      (g : (Fin m → R) →ₗ[R] (Fin n → R)),
      Function.Surjective f ∧ Function.Exact g f :=
  FinitePresentation.exists_fin_exact R M

section RestrictScalars

variable (R : Type u) {S : Type v} {N : Type w}
variable [Ring R] [Ring S] [AddCommGroup N]
variable [Module R S] [Module R N] [Module S N]
variable [IsScalarTower R S S] [IsScalarTower R S N] [Module.IsCoherent R S]

/-- A finitely presented module over a ring coherent as a module over the base ring
is coherent for its given compatible base action.

Both rings may be noncommutative, and the scalar and module universes are independent. -/
theorem FinitePresentation.isCoherent_restrictScalars [Module.FinitePresentation S N] :
    Module.IsCoherent R N := by
  obtain ⟨n, m, φ, ψ, hφ, hψφ⟩ := Module.FinitePresentation.exists_fin_exact S N
  let φR : (Fin n → S) →ₗ[R] N := φ.restrictScalars R
  let ψR : (Fin m → S) →ₗ[R] (Fin n → S) := ψ.restrictScalars R
  have hφR : Function.Surjective φR := hφ
  have hExactR : Function.Exact ψR φR := hψφ
  let _ : Module.IsCoherent R (Fin n → S) := Module.IsCoherent.pi
  let _ : Module.Finite R (Fin m → S) := Module.Finite.pi
  have hK : (LinearMap.ker φR).FG := by
    rw [hExactR.linearMap_ker_eq]
    exact Submodule.fg_range ψR
  let _ : Module.IsCoherent R ((Fin n → S) ⧸ LinearMap.ker φR) :=
    Module.IsCoherent.quotient _ hK
  exact Module.IsCoherent.of_equiv (φR.quotKerEquivOfSurjective hφR)

/-- If the scalar ring is coherent over the base ring, coherence over either ring
is equivalent for the given compatible module structures. -/
theorem isCoherent_restrictScalars_iff :
    Module.IsCoherent R N ↔ Module.IsCoherent S N := by
  constructor
  · intro h
    let _ : Module.IsCoherent R N := h
    exact Module.IsCoherent.of_restrictScalars R
  · intro h
    let _ : Module.IsCoherent S N := h
    exact Module.FinitePresentation.isCoherent_restrictScalars R (S := S)

/-- If the scalar ring is coherent over the base ring, coherence over the base
is equivalent to finite presentation over the scalar ring. -/
theorem isCoherent_restrictScalars_iff_finitePresentation :
    Module.IsCoherent R N ↔ Module.FinitePresentation S N := by
  constructor
  · intro h
    let _ : Module.IsCoherent S N := (isCoherent_restrictScalars_iff R).mp h
    infer_instance
  · intro h
    let _ : Module.FinitePresentation S N := h
    exact Module.FinitePresentation.isCoherent_restrictScalars R (S := S)

end RestrictScalars

variable {R : Type u} [Ring R]

namespace FinitePresentation

variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A finitely presented module over a coherent ring is coherent. -/
theorem isCoherent [IsCoherentRing R] [Module.FinitePresentation R M] :
    Module.IsCoherent R M :=
  Module.FinitePresentation.isCoherent_restrictScalars R (S := R)

/-- The kernel of a linear map between finitely presented modules over a
coherent ring is finitely presented. -/
theorem ker [IsCoherentRing R]
    {N : Type w} [AddCommGroup N] [Module R N]
    [Module.FinitePresentation R M] [Module.FinitePresentation R N]
    (f : M →ₗ[R] N) : Module.FinitePresentation R (LinearMap.ker f) := by
  let _ : Module.IsCoherent R M := Module.FinitePresentation.isCoherent
  let _ : Module.IsCoherent R N := Module.FinitePresentation.isCoherent
  exact Module.IsCoherent.finitePresentation_ker f

/-- In a sequence of five modules that is exact at the middle three, the middle
module is finitely presented if the first module is finite and the second,
fourth, and fifth modules are finitely presented. -/
theorem of_exact_five [IsCoherentRing R]
    {M1 : Type v1} {M2 : Type v2} {M3 : Type v3}
    {M4 : Type v4} {M5 : Type v5}
    [AddCommGroup M1] [Module R M1]
    [AddCommGroup M2] [Module R M2]
    [AddCommGroup M3] [Module R M3]
    [AddCommGroup M4] [Module R M4]
    [AddCommGroup M5] [Module R M5]
    [Module.Finite R M1]
    [Module.FinitePresentation R M2]
    [Module.FinitePresentation R M4]
    [Module.FinitePresentation R M5]
    (f12 : M1 →ₗ[R] M2) (f23 : M2 →ₗ[R] M3)
    (f34 : M3 →ₗ[R] M4) (f45 : M4 →ₗ[R] M5)
    (h2 : Function.Exact f12 f23)
    (h3 : Function.Exact f23 f34)
    (h4 : Function.Exact f34 f45) :
    Module.FinitePresentation R M3 := by
  let _ : Module.FinitePresentation R (LinearMap.range f23) :=
    Module.finitePresentation_of_surjective f23.rangeRestrict
      (LinearMap.surjective_rangeRestrict f23) (by
        rw [LinearMap.ker_rangeRestrict, h2.linearMap_ker_eq]
        exact Submodule.fg_range f12)
  let _ : Module.FinitePresentation R (LinearMap.ker f34) := by
    rw [h3.linearMap_ker_eq]
    infer_instance
  let _ : Module.FinitePresentation R (LinearMap.range f34) := by
    rw [← h4.linearMap_ker_eq]
    exact Module.FinitePresentation.ker f45
  let _ : Module.FinitePresentation R (LinearMap.ker f34.rangeRestrict) := by
    rw [LinearMap.ker_rangeRestrict]
    infer_instance
  exact Module.finitePresentation_of_ker f34.rangeRestrict
    (LinearMap.surjective_rangeRestrict f34)

end FinitePresentation

/-- Over a coherent ring, a module is coherent exactly when it is finitely
presented. -/
theorem isCoherent_iff_finitePresentation
    {M : Type v} [AddCommGroup M] [Module R M] [IsCoherentRing R] :
    Module.IsCoherent R M ↔ Module.FinitePresentation R M := by
  constructor
  · intro h
    let _ : Module.IsCoherent R M := h
    infer_instance
  · intro h
    let _ : Module.FinitePresentation R M := h
    exact Module.FinitePresentation.isCoherent

end Ring

end Module
