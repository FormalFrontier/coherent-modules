/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Formal Frontier AI agents
-/
module

public import CoherentModules.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Abelian.Subcategory

/-!
# The abelian category of coherent modules

This file packages coherent modules over an arbitrary ring as an object property
of `ModuleCat`.  The property contains zero and is closed under isomorphisms,
kernels, cokernels, and finite products.  Consequently, mathlib's generic
full-subcategory construction gives the category of coherent modules an
`Abelian` instance.

## Main declarations

* `ModuleCat.isCoherent`: the coherent-module object property.
* `CoherentModuleCat`: the full subcategory of coherent modules.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

variable (R : Type u) [Ring R]

/-- The property that the underlying module of an object of `ModuleCat R` is coherent. -/
def isCoherent : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ Module.IsCoherent R M

variable {R} in
/-- Membership in `ModuleCat.isCoherent` is the unbundled coherent-module predicate. -/
lemma isCoherent_iff (M : ModuleCat.{v} R) :
    isCoherent R M ↔ Module.IsCoherent R M :=
  Iff.rfl

instance isCoherentIsClosedUnderIsomorphisms :
    (isCoherent.{u, v} R).IsClosedUnderIsomorphisms where
  of_iso e h := by
    let _ : Module.IsCoherent R _ := h
    exact Module.IsCoherent.of_equiv e.toLinearEquiv

instance isCoherentContainsZero :
    (isCoherent.{u, v} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit,
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance, by
      change Module.IsCoherent R PUnit
      infer_instance⟩

instance isCoherentIsClosedUnderKernels :
    (isCoherent.{u, v} R).IsClosedUnderKernels where
  kernels_le := by
    rintro K ⟨f, k, hk, ⟨hX, hY⟩⟩
    let _ : Module.IsCoherent R _ := hX
    let _ : Module.IsCoherent R _ := hY
    let _ : Module.IsCoherent R (LinearMap.ker f.hom) := Module.IsCoherent.ker f.hom
    let e :=
      hk.conePointUniqueUpToIso (kernelIsKernel f) ≪≫ ModuleCat.kernelIsoKer f
    exact Module.IsCoherent.of_equiv e.symm.toLinearEquiv

instance isCoherentIsClosedUnderCokernels :
    (isCoherent.{u, v} R).IsClosedUnderCokernels where
  cokernels_le := by
    rintro K ⟨f, k, hk, ⟨hX, hY⟩⟩
    let _ : Module.IsCoherent R _ := hX
    let _ : Module.IsCoherent R _ := hY
    let _ : Module.IsCoherent R (_ ⧸ LinearMap.range f.hom) :=
      Module.IsCoherent.cokernel f.hom
    let e :=
      hk.coconePointUniqueUpToIso (cokernelIsCokernel f) ≪≫
        ModuleCat.cokernelIsoRangeQuotient f
    exact Module.IsCoherent.of_equiv e.symm.toLinearEquiv

instance isCoherentIsClosedUnderBinaryProducts :
    (isCoherent.{u, v} R).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro Z ⟨p⟩
    let X := p.diag.obj ⟨WalkingPair.left⟩
    let Y := p.diag.obj ⟨WalkingPair.right⟩
    let _ : Module.IsCoherent R X := p.prop_diag_obj ⟨WalkingPair.left⟩
    let _ : Module.IsCoherent R Y := p.prop_diag_obj ⟨WalkingPair.right⟩
    let e : ModuleCat.of R (X × Y) ≅ Z := IsLimit.conePointUniqueUpToIso
      (ModuleCat.binaryProductLimitCone X Y).isLimit
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)
    apply (isCoherent R).prop_of_iso e
    change Module.IsCoherent R (X × Y)
    infer_instance

instance isCoherentIsClosedUnderFiniteProducts :
    (isCoherent.{u, v} R).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

end ModuleCat

/-- The full subcategory of coherent modules over `R`.

Its `Abelian` instance is supplied by
`Mathlib.CategoryTheory.Abelian.Subcategory` from the closure instances above. -/
abbrev CoherentModuleCat (R : Type u) [Ring R] :=
  (ModuleCat.isCoherent.{u, v} R).FullSubcategory
