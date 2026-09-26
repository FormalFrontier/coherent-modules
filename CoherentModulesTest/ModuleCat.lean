/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: The original examples are retained from the reviewed project history
-/
module

import CoherentModules
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.Data.ZMod.Basic

/-!
External-use checks for the coherent-module object property and its abelian
full subcategory.
-/

namespace CoherentModulesTest.ModuleCat

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

private theorem objectPropertyCriterion (R : Type u) [Ring R] (M : ModuleCat.{v} R) :
    ModuleCat.isCoherent R M ↔ Module.IsCoherent R M :=
  ModuleCat.isCoherent_iff M

private theorem isomorphismClosure (R : Type u) [Ring R] :
    (ModuleCat.isCoherent.{u, v} R).IsClosedUnderIsomorphisms :=
  inferInstance

private theorem containsZero (R : Type u) [Ring R] :
    (ModuleCat.isCoherent.{u, v} R).ContainsZero :=
  inferInstance

private theorem kernelClosure (R : Type u) [Ring R] :
    (ModuleCat.isCoherent.{u, v} R).IsClosedUnderKernels :=
  inferInstance

private theorem cokernelClosure (R : Type u) [Ring R] :
    (ModuleCat.isCoherent.{u, v} R).IsClosedUnderCokernels :=
  inferInstance

private theorem finiteProductClosure (R : Type u) [Ring R] :
    (ModuleCat.isCoherent.{u, v} R).IsClosedUnderFiniteProducts :=
  inferInstance

@[instance_reducible]
private noncomputable def abelianCategory (R : Type u) [Ring R] : Abelian (CoherentModuleCat.{u, v} R) :=
  inferInstance

private noncomputable def coherentObject (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.IsCoherent R M] : CoherentModuleCat.{u, v} R :=
  ⟨ModuleCat.of R M, (ModuleCat.isCoherent_iff _).2 inferInstance⟩

private theorem transportObject (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
    [Module.IsCoherent R M] (N : ModuleCat.{v} R) (e : ModuleCat.of R M ≅ N) :
    ModuleCat.isCoherent R N :=
  (ModuleCat.isCoherent R).prop_of_iso e
    ((ModuleCat.isCoherent_iff _).2 inferInstance)

private theorem zeroObject (R : Type u) [Ring R] :
    ModuleCat.isCoherent.{u, v} R (0 : ModuleCat.{v} R) :=
  (ModuleCat.isCoherent R).prop_zero

private theorem zeroMapKernel (R : Type u) [Ring R] (M : Type v) (N : Type v)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.IsCoherent R M] [Module.IsCoherent R N] :
  ModuleCat.isCoherent R
      (kernel (0 : ModuleCat.of R M ⟶ ModuleCat.of R N)) :=
  (ModuleCat.isCoherent R).prop_kernel 0
    ((ModuleCat.isCoherent_iff _).2 inferInstance)
    ((ModuleCat.isCoherent_iff _).2 inferInstance)

private theorem zeroMapCokernel (R : Type u) [Ring R] (M : Type v) (N : Type v)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.IsCoherent R M] [Module.IsCoherent R N] :
  ModuleCat.isCoherent R
      (cokernel (0 : ModuleCat.of R M ⟶ ModuleCat.of R N)) :=
  (ModuleCat.isCoherent R).prop_cokernel 0
    ((ModuleCat.isCoherent_iff _).2 inferInstance)
    ((ModuleCat.isCoherent_iff _).2 inferInstance)

private theorem emptyProduct (R : Type u) [Ring R] :
    ModuleCat.isCoherent R
      (∏ᶜ fun _ : Fin 0 ↦ ModuleCat.of R PUnit) :=
  (ModuleCat.isCoherent R).prop_product fun i ↦ Fin.elim0 i

@[instance_reducible]
private noncomputable def zeroRingAbelianCategory : Abelian (CoherentModuleCat.{0, 0} (ZMod 1)) :=
  inferInstance

/-- The object property remains definitionally equal to the unbundled predicate. -/
private theorem objectPropertyReduction (R : Type u) [Ring R] (M : ModuleCat.{v} R) :
    ModuleCat.isCoherent R M ↔ Module.IsCoherent R M := Iff.rfl

/-- The public category abbreviation retains its underlying full subcategory. -/
private theorem categoryReduction (R : Type u) [Ring R] :
    CoherentModuleCat.{u, v} R = (ModuleCat.isCoherent.{u, v} R).FullSubcategory := rfl

-- Selected named-client axiom checks, not a complete release census.
#print axioms objectPropertyCriterion
#print axioms isomorphismClosure
#print axioms containsZero
#print axioms kernelClosure
#print axioms cokernelClosure
#print axioms finiteProductClosure
#print axioms abelianCategory
#print axioms coherentObject
#print axioms transportObject
#print axioms zeroObject
#print axioms zeroMapKernel
#print axioms zeroMapCokernel
#print axioms emptyProduct
#print axioms zeroRingAbelianCategory
#print axioms objectPropertyReduction
#print axioms categoryReduction

end CoherentModulesTest.ModuleCat
