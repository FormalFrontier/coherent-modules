/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finitely generated submodules of localized semimodules

Every finitely generated submodule of a localized semimodule is the localization
of a finitely generated submodule of the original semimodule. A common denominator
for a finite generating set gives the original submodule. No finiteness assumption
on the ambient semimodule is needed.

## Main declarations

* `Submodule.FG.exists_localized'_eq`: a finitely generated submodule of a
  localized semimodule has a finitely generated representative before localization.

## References

The proof uses Christian Merten's common-denominator API in
`Mathlib.Algebra.Module.LocalizedModule.Int` and Andrew Yang's submodule-localization
API in `Mathlib.Algebra.Module.LocalizedModule.Submodule`.
-/

@[expose] public section

universe uR uA uX uY

open scoped Pointwise

/-- Every finitely generated submodule of a localized semimodule is the localization
of some finitely generated submodule of the original semimodule. Neither ambient
semimodule is required to be finitely generated. -/
theorem Submodule.FG.exists_localized'_eq
    {R : Type uR} [CommSemiring R]
    {A : Type uA} [CommSemiring A] [Algebra R A]
    {X : Type uX} [AddCommMonoid X] [Module R X]
    {Y : Type uY} [AddCommMonoid Y] [Module R Y]
    [Module A Y] [IsScalarTower R A Y]
    (U : Submonoid R) [IsLocalization U A]
    (f : X →ₗ[R] Y) [IsLocalizedModule U f]
    {N : Submodule A Y} (hN : N.FG) :
    ∃ P : Submodule R X, P.FG ∧ P.localized' A U f = N := by
  classical
  obtain ⟨t, htfinite, htspan⟩ := Submodule.fg_def.mp hN
  let s : Finset Y := htfinite.toFinset
  let T : Finset X := IsLocalizedModule.finsetIntegerMultiple U f s
  refine ⟨Submodule.span R (T : Set X), Submodule.fg_span T.finite_toSet, ?_⟩
  rw [Submodule.localized'_span]
  rw [IsLocalizedModule.finsetIntegerMultiple_image]
  rw [show (s : Set Y) = t from htfinite.coe_toFinset]
  let y := IsLocalizedModule.commonDenomOfFinset U f s
  have hfun : (fun z : Y ↦ y • z) =
      (fun z : Y ↦ algebraMap R A (y : R) • z) := by
    funext z
    rw [Submonoid.smul_def, algebraMap_smul]
  have hsmul : y • t = algebraMap R A (y : R) • t := by
    simpa only [← Set.image_smul] using congrArg (fun g : Y → Y ↦ g '' t) hfun
  rw [hsmul, Submodule.span_smul_eq_of_isUnit]
  · exact htspan
  · exact IsLocalization.map_units A y
