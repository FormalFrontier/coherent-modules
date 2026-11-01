/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# Tensor products and kernels over semirings

If left tensoring preserves finite limits in the category of semimodules, it
carries a linear kernel to the range of the tensored kernel inclusion. This uses
the concrete categorical kernel and uniqueness of limit cones; no additive
inverses or subtractivity are required.

## References

The comparison uses Mathlib's preservation of kernel forks and uniqueness of
limits, together with the concrete semimodule kernel.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

/-- Left tensoring with a semimodule which preserves finite limits carries a
linear kernel to the range of the tensored kernel inclusion. -/
theorem LinearMap.ker_lTensor_eq_of_preservesFiniteLimits
    {R : Type u} [CommSemiring R]
    (S M N : Type u) [AddCommMonoid S] [Module R S]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [PreservesFiniteLimits
      (tensorLeft (C := SemimoduleCat.{u} R) (SemimoduleCat.of R S))]
    (f : M →ₗ[R] N) :
    LinearMap.ker (f.lTensor S) = LinearMap.range ((LinearMap.ker f).subtype.lTensor S) := by
  let F := tensorLeft (C := SemimoduleCat.{u} R) (SemimoduleCat.of R S)
  let g : SemimoduleCat.of R M ⟶ SemimoduleCat.of R N := SemimoduleCat.ofHom f
  let : F.PreservesZeroMorphisms := ⟨fun X Y ↦ by
    apply SemimoduleCat.hom_ext
    change (0 : X →ₗ[R] Y).lTensor S = 0
    exact LinearMap.lTensor_zero S⟩
  let h := (SemimoduleCat.kernelCone g).mapIsLimit (SemimoduleCat.kernelIsLimit g) F
  let e := IsLimit.conePointUniqueUpToIso h (SemimoduleCat.kernelIsLimit (F.map g))
  have he : e.inv ≫ F.map (SemimoduleCat.kernelCone g).ι =
      (SemimoduleCat.kernelCone (F.map g)).ι := by
    simpa only [Fork.app_zero_eq_ι, KernelFork.map_ι] using
      IsLimit.conePointUniqueUpToIso_inv_comp h
        (SemimoduleCat.kernelIsLimit (F.map g)) WalkingParallelPair.zero
  ext x
  constructor
  · intro hx
    refine ⟨e.inv ⟨x, hx⟩, ?_⟩
    exact ConcreteCategory.congr_hom he ⟨x, hx⟩
  · rintro ⟨y, rfl⟩
    apply LinearMap.mem_ker.mpr
    change (f.lTensor S) (((LinearMap.ker f).subtype.lTensor S) y) = 0
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
      LinearMap.comp_ker_subtype, LinearMap.lTensor_zero, LinearMap.zero_apply]
