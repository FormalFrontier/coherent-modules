/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.Module.LocalizedModule.Finite
public import CoherentModules.LinearAlgebra.TensorProduct.Annihilator
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Finitely generated submodules and annihilators under localization

Every finitely generated submodule of a localized semimodule is the localization
of a finitely generated submodule of the original semimodule. A common denominator
for a finite generating set gives the original submodule. No finiteness assumption
on the ambient semimodule is needed.

For a finitely generated semimodule, extension of its annihilator is the annihilator
of any standard localized-module realization. A uniform multiplier on a finite
generating family proves the reverse inclusion; the forward inclusion already
follows from the tensor-product annihilator containment.

## Main declarations

* `Submodule.FG.exists_localized'_eq`: a finitely generated submodule of a
  localized semimodule has a finitely generated representative before localization.
* `IsLocalizedModule.map_annihilator`: localization commutes with the annihilator
  of a finitely generated semimodule.

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

universe uM uN

/-- Extension of the annihilator of a finitely generated semimodule is the annihilator
of any of its standard localized-module realizations. -/
theorem IsLocalizedModule.map_annihilator
    {R : Type uR} [CommSemiring R] (T : Submonoid R)
    {A : Type uA} [CommSemiring A] [Algebra R A] [IsLocalization T A]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N] [Module A N]
    [IsScalarTower R A N]
    (f : M →ₗ[R] N) [IsLocalizedModule T f] [Module.Finite R M] :
    Ideal.map (algebraMap R A) (Module.annihilator R M) =
      Module.annihilator A N := by
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    let e := (IsLocalizedModule.isBaseChange T A f).equiv
    rw [← e.annihilator_eq]
    exact TensorProduct.annihilator_le_comap_annihilator R A M
  · intro q hq
    rw [Module.mem_annihilator] at hq
    obtain ⟨⟨a, t⟩, hqt⟩ := IsLocalization.surj T q
    have hcomp : f.comp (a • (LinearMap.id : M →ₗ[R] M)) =
        f.comp (0 : M →ₗ[R] M) := by
      ext m
      have hkill : algebraMap R A a • f m = 0 := by
        rw [← hqt, mul_comm q, mul_smul, hq (f m), smul_zero]
      simpa only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
        LinearMap.zero_apply, map_zero, map_smul, IsScalarTower.algebraMap_smul] using hkill
    obtain ⟨s, hs⟩ :=
      (IsLocalizedModule.comp_eq_iff_exists_smul_eq T f
        (a • (LinearMap.id : M →ₗ[R] M)) (0 : M →ₗ[R] M)).mp hcomp
    have hsa : (s : R) * a ∈ Module.annihilator R M := by
      rw [Module.mem_annihilator]
      intro m
      have hm := congrArg (fun k : M →ₗ[R] M => k m) hs
      simpa only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply,
        smul_zero, mul_smul, Submonoid.smul_def] using hm
    apply (IsLocalization.mem_map_algebraMap_iff T A).mpr
    refine ⟨⟨⟨(s : R) * a, hsa⟩, t * s⟩, ?_⟩
    change q * algebraMap R A ((t : R) * (s : R)) =
      algebraMap R A ((s : R) * a)
    rw [map_mul, ← mul_assoc, hqt, map_mul, mul_comm]
