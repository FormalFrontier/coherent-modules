/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
Contributors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Concrete kernels of semimodule morphisms

For an arbitrary semiring, the kernel submodule of a linear map, with its subtype
inclusion, is a categorical kernel in `SemimoduleCat`. The coefficient and carrier
universes are independent. Over a ring, the comparison with the concrete kernel in
`ModuleCat` preserves the underlying elements.

## Main declarations

* `SemimoduleCat.kernelCone`: the fork with point `LinearMap.ker` and subtype inclusion.
* `SemimoduleCat.kernelIsLimit`: the universal property of this fork.
* `SemimoduleCat.hasKernels_semimoduleCat`: existence of kernels over a semiring.
* `ModuleCat.kernelCone_semimodule_hom_apply`: agreement with the module kernel
  through the existing equivalence and uniqueness of limit cone points.

## References

The kernel construction and universal-property proof generalize Markus Himmel's
formalization in `Mathlib.Algebra.Category.ModuleCat.Kernels`.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace SemimoduleCat

variable {R : Type u} [Semiring R] {M N : SemimoduleCat.{v} R}

/-- The kernel fork whose point is the kernel submodule and whose map is its inclusion. -/
def kernelCone (f : M ⟶ N) : KernelFork f :=
  KernelFork.ofι (ofHom (LinearMap.ker f.hom).subtype)
    (hom_ext <| LinearMap.comp_ker_subtype f.hom)

/-- The underlying type of the kernel fork is the kernel submodule. -/
@[simp]
theorem kernelCone_pt_coe (f : M ⟶ N) :
    ((kernelCone f).pt : Type v) = (LinearMap.ker f.hom : Type v) :=
  rfl

/-- The inclusion of the kernel fork is the subtype linear map. -/
@[simp]
theorem kernelCone_ι_hom (f : M ⟶ N) :
    (kernelCone f).ι.hom = (LinearMap.ker f.hom).subtype :=
  rfl

/-- The inclusion of the kernel fork sends a kernel element to its underlying element. -/
theorem kernelCone_ι_apply (f : M ⟶ N) (x : LinearMap.ker f.hom) :
    (kernelCone f).ι x = (x : M) :=
  rfl

/-- The kernel submodule of a semimodule morphism is a categorical kernel. -/
def kernelIsLimit (f : M ⟶ N) : IsLimit (kernelCone f) :=
  Fork.IsLimit.mk _
    (fun s => ofHom <|
      LinearMap.codRestrict f.hom.ker (Fork.ι s).hom fun c =>
        LinearMap.mem_ker.2 <| by simp [← ConcreteCategory.comp_apply])
    (fun _ => hom_ext <| LinearMap.subtype_comp_codRestrict _ _ _) fun s m h =>
      hom_ext <| LinearMap.ext fun x => Subtype.ext_iff.2 (by simp [← h]; rfl)

/-- Semimodules over a semiring have kernels, given by kernel submodule inclusions. -/
theorem hasKernels_semimoduleCat : HasKernels (SemimoduleCat.{v} R) :=
  ⟨fun f => HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

end SemimoduleCat

namespace ModuleCat

/-- The comparison from the module kernel to the semimodule kernel preserves elements.

The comparison is the unique isomorphism of limit cone points after mapping the
module kernel along `ModuleCat.equivalenceSemimoduleCat`.
-/
theorem kernelCone_semimodule_hom_apply
    {R : Type u} [Ring R] {M N : ModuleCat.{v} R}
    (f : M ⟶ N) (x : (ModuleCat.kernelCone f).pt) :
    let E : ModuleCat.{v} R ≌ SemimoduleCat.{v} R :=
      ModuleCat.equivalenceSemimoduleCat (R := R)
    (show LinearMap.ker (E.functor.map f).hom from
      (IsLimit.conePointUniqueUpToIso
        ((ModuleCat.kernelCone f).mapIsLimit (ModuleCat.kernelIsLimit f) E.functor)
        (SemimoduleCat.kernelIsLimit (E.functor.map f))).hom x).val =
      (show LinearMap.ker f.hom from x).val := by
  let E : ModuleCat.{v} R ≌ SemimoduleCat.{v} R :=
    ModuleCat.equivalenceSemimoduleCat (R := R)
  have h :
      (IsLimit.conePointUniqueUpToIso
        ((ModuleCat.kernelCone f).mapIsLimit (ModuleCat.kernelIsLimit f) E.functor)
        (SemimoduleCat.kernelIsLimit (E.functor.map f))).hom ≫
          (SemimoduleCat.kernelCone (E.functor.map f)).ι =
        E.functor.map (ModuleCat.kernelCone f).ι := by
    simpa only [Fork.app_zero_eq_ι, KernelFork.map_ι] using
      IsLimit.conePointUniqueUpToIso_hom_comp
        ((ModuleCat.kernelCone f).mapIsLimit (ModuleCat.kernelIsLimit f) E.functor)
        (SemimoduleCat.kernelIsLimit (E.functor.map f)) WalkingParallelPair.zero
  exact ConcreteCategory.congr_hom h x

end ModuleCat
