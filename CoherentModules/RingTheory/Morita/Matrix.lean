/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

Portions adapted from Mathlib/RingTheory/Morita/Matrix.lean:
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import CoherentModules.LinearAlgebra.Matrix.ReconstructionCoherence
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The equivalence between semimodules and matrix semimodules

Columns and the range of a diagonal matrix unit give inverse functors between the existing
categories `SemimoduleCat R` and `SemimoduleCat (Matrix I I R)`. The coefficient action on a
matrix semimodule is restriction along `Matrix.scalar I`. The unit is inverse coefficient
recovery, and the counit is coordinate reconstruction.

The common carrier universe is `max uI v`, where `I : Type uI`. This closes columns and
coordinate ranges without a bound on the scalar universe. The raw reconstruction results
retain their independent carrier universes.

Over a ring, natural isomorphisms compare these functors with Mathlib's matrix-module
functors through `ModuleCat.equivalenceSemimoduleCat`. Their components are identity on
vectors and range representatives. Coefficient recovery agrees with the old sum map by
the support-sum identity, not by identifying sum with evaluation definitionally.

## References

The categorical packaging follows Mathlib's `RingTheory.Morita.Matrix`, by Yunzhou Xie and
Jujian Zhang. The semiring reconstruction and coherence are supplied by
`Matrix.Module.coordinateReconstruction` and `Matrix.Module.coefficientEquiv`.
-/

@[expose] public section

universe uR uI v

open CategoryTheory
open scoped Matrix.Module

section Semiring

variable (R : Type uR) (I : Type uI) [Semiring R] [Fintype I] [DecidableEq I]

namespace SemimoduleCat

/-- The column functor, with the matrix action built from the given coefficient action. -/
def toMatrixModCat : SemimoduleCat.{max uI v} R ⥤
    SemimoduleCat.{max uI v} (Matrix I I R) where
  obj M :=
    letI : Module (Matrix I I R) (I → M) := Matrix.Module.matrixModuleSemiring I R M
    SemimoduleCat.of (Matrix I I R) (I → M)
  map f := SemimoduleCat.ofHom (LinearMap.matrixModuleMap I f.hom)
  map_id _ := SemimoduleCat.hom_ext (LinearMap.matrixModuleMap_id (I := I))
  map_comp f g := SemimoduleCat.hom_ext (LinearMap.matrixModuleMap_comp I f.hom g.hom)

/-- The column functor has the function type as its carrier. -/
@[simp]
lemma coe_toMatrixModCat_obj (M : SemimoduleCat.{max uI v} R) :
    ((toMatrixModCat R I).obj M : Type (max uI v)) = (I → M) := rfl

/-- The map of the column functor is the existing coordinatewise linear map. -/
@[simp]
lemma toMatrixModCat_map_hom {M M' : SemimoduleCat.{max uI v} R} (f : M ⟶ M') :
    ((toMatrixModCat R I).map f).hom = LinearMap.matrixModuleMap I f.hom := rfl

/-- The column functor applies a morphism at each coordinate. -/
lemma toMatrixModCat_map_apply {M M' : SemimoduleCat.{max uI v} R}
    (f : M ⟶ M') (x : I → M) (i : I) :
    (toMatrixModCat R I).map f x i = f (x i) := rfl

/-- The column functor preserves zero morphisms. -/
@[simp]
lemma toMatrixModCat_map_zero (M M' : SemimoduleCat.{max uI v} R) :
    (toMatrixModCat R I).map (0 : M ⟶ M') = 0 :=
  SemimoduleCat.hom_ext (map_zero (LinearMap.matrixModuleMap I))

/-- The column functor is additive on morphisms. -/
@[simp]
lemma toMatrixModCat_map_add {M M' : SemimoduleCat.{max uI v} R} (f g : M ⟶ M') :
    (toMatrixModCat R I).map (f + g) =
      (toMatrixModCat R I).map f + (toMatrixModCat R I).map g :=
  SemimoduleCat.hom_ext (map_add (LinearMap.matrixModuleMap I) f.hom g.hom)

end SemimoduleCat

namespace MatrixSemimoduleCat

open Matrix.Module

variable {I}

/-- The coordinate-range functor. Its ambient coefficient action is scalar restriction. -/
def toSemimoduleCat (k : I) : SemimoduleCat.{max uI v} (Matrix I I R) ⥤
    SemimoduleCat.{max uI v} R where
  obj N :=
    letI : Module R N := Module.compHom N (Matrix.scalar I)
    SemimoduleCat.of R (coordinateSubmodule R I N k)
  map f := SemimoduleCat.ofHom (coordinateMap R I k f.hom)
  map_id _ := SemimoduleCat.hom_ext (coordinateMap_id R I k)
  map_comp f g := SemimoduleCat.hom_ext (coordinateMap_comp R I k f.hom g.hom)

/-- The coordinate functor uses the original linear-map range as its carrier. -/
@[simp]
lemma coe_toSemimoduleCat_obj (k : I) (N : SemimoduleCat.{max uI v} (Matrix I I R)) :
    ((toSemimoduleCat R k).obj N : Type (max uI v)) = coordinateSubmodule R I N k := rfl

/-- The underlying map of the coordinate functor is scalar and image restriction. -/
@[simp]
lemma toSemimoduleCat_map_hom (k : I)
    {N N' : SemimoduleCat.{max uI v} (Matrix I I R)} (f : N ⟶ N') :
    ((toSemimoduleCat R k).map f).hom = coordinateMap R I k f.hom := rfl

/-- The coordinate functor does not change the ambient representative of a morphism. -/
lemma coe_toSemimoduleCat_map_apply (k : I)
    {N N' : SemimoduleCat.{max uI v} (Matrix I I R)} (f : N ⟶ N')
    (x : coordinateSubmodule R I N k) :
    Subtype.val ((toSemimoduleCat R k).map f x : coordinateSubmodule R I N' k) =
      f (x : N) := rfl

/-- The coordinate functor preserves zero morphisms. -/
@[simp]
lemma toSemimoduleCat_map_zero (k : I)
    (N N' : SemimoduleCat.{max uI v} (Matrix I I R)) :
    (toSemimoduleCat R k).map (0 : N ⟶ N') = 0 :=
  SemimoduleCat.hom_ext (map_zero (coordinateMap R I k))

/-- The coordinate functor is additive on morphisms. -/
@[simp]
lemma toSemimoduleCat_map_add (k : I)
    {N N' : SemimoduleCat.{max uI v} (Matrix I I R)} (f g : N ⟶ N') :
    (toSemimoduleCat R k).map (f + g) =
      (toSemimoduleCat R k).map f + (toSemimoduleCat R k).map g :=
  SemimoduleCat.hom_ext (map_add (coordinateMap R I k) f.hom g.hom)

/-- Natural coefficient recovery from the coordinate range of a column module. -/
def coefficientIso (k : I) :
    SemimoduleCat.toMatrixModCat R I ⋙ toSemimoduleCat R k ≅
      𝟭 (SemimoduleCat.{max uI v} R) :=
  NatIso.ofComponents (fun M => (coefficientEquiv R I M k).toModuleIsoₛ)
    (fun f => SemimoduleCat.hom_ext (coefficientEquiv_naturality R I k f.hom).symm)

/-- Natural reconstruction of an arbitrary matrix semimodule from its coordinate range. -/
def counitIso (k : I) :
    toSemimoduleCat R k ⋙ SemimoduleCat.toMatrixModCat R I ≅
      𝟭 (SemimoduleCat.{max uI v} (Matrix I I R)) :=
  NatIso.ofComponents (fun N => (coordinateReconstruction R I N k).toModuleIsoₛ)
    (fun f => SemimoduleCat.hom_ext (coordinateReconstruction_naturality R I k f.hom).symm)

/-- Natural coefficient recovery is evaluation at the chosen coordinate. -/
lemma coefficientIso_hom_app_apply (k : I) (M : SemimoduleCat.{max uI v} R)
    (x : coordinateSubmodule R I (I → M) k) :
    (coefficientIso R k).hom.app M x = (x : I → M) k :=
  coefficientEquiv_apply R I M k x

/-- Inverse natural coefficient recovery inserts a supported vector. -/
lemma coe_coefficientIso_inv_app_apply (k : I) (M : SemimoduleCat.{max uI v} R) (x : M) :
    Subtype.val ((coefficientIso R k).inv.app M x : coordinateSubmodule R I (I → M) k) =
      Pi.single k x := rfl

/-- The counit sums the translated representatives of the coordinate ranges. -/
lemma counitIso_hom_app_apply (k : I) (N : SemimoduleCat.{max uI v} (Matrix I I R))
    (x : I → coordinateSubmodule R I N k) :
    (counitIso R k).hom.app N x = ∑ i, Matrix.single i k (1 : R) • (x i : N) := rfl

/-- The inverse counit takes matrix-unit coordinates in the original matrix action. -/
lemma coe_counitIso_inv_app_apply (k : I) (N : SemimoduleCat.{max uI v} (Matrix I I R))
    (x : N) (i : I) :
    Subtype.val ((counitIso R k).inv.app N x i : coordinateSubmodule R I N k) =
      Matrix.single k i (1 : R) • x := rfl

/-- Changing the chosen index gives a natural isomorphism of coordinate functors. -/
def coordinateChangeIso (k l : I) : toSemimoduleCat R k ≅ toSemimoduleCat R l :=
  NatIso.ofComponents (fun N => (coordinateChange R I N k l).toModuleIsoₛ)
    (fun f => SemimoduleCat.hom_ext (coordinateChange_naturality R I k l f.hom))

/-- The natural change of coordinate acts by the corresponding matrix unit. -/
lemma coe_coordinateChangeIso_hom_app_apply (k l : I)
    (N : SemimoduleCat.{max uI v} (Matrix I I R)) (x : coordinateSubmodule R I N k) :
    Subtype.val ((coordinateChangeIso R k l).hom.app N x : coordinateSubmodule R I N l) =
      Matrix.single l k (1 : R) • (x : N) :=
  coe_coordinateChange_apply R I N k l x

/-- The inverse natural change of coordinate acts by the opposite matrix unit. -/
lemma coe_coordinateChangeIso_inv_app_apply (k l : I)
    (N : SemimoduleCat.{max uI v} (Matrix I I R)) (x : coordinateSubmodule R I N l) :
    Subtype.val ((coordinateChangeIso R k l).inv.app N x : coordinateSubmodule R I N k) =
      Matrix.single k l (1 : R) • (x : N) :=
  coe_coordinateChange_symm_apply R I N k l x

/-- Changing an index to itself is the identity natural isomorphism. -/
@[simp]
lemma coordinateChangeIso_refl (k : I) :
    coordinateChangeIso R k k = Iso.refl (toSemimoduleCat R k) := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  exact SemimoduleCat.hom_ext
    (congrArg LinearEquiv.toLinearMap (coordinateChange_refl R I N k))

/-- Successive natural changes of coordinate compose without additional choices. -/
@[simp]
lemma coordinateChangeIso_trans (k l m : I) :
    coordinateChangeIso R k l ≪≫ coordinateChangeIso R l m = coordinateChangeIso R k m := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  exact SemimoduleCat.hom_ext
    (congrArg LinearEquiv.toLinearMap (coordinateChange_trans R I N k l m))

/-- Reconstruction is compatible with the natural change of coordinate functor. -/
lemma counitIso_coordinateChange (k l : I)
    (N : SemimoduleCat.{max uI v} (Matrix I I R)) :
    (SemimoduleCat.toMatrixModCat R I).map ((coordinateChangeIso R k l).hom.app N) ≫
        (counitIso R l).hom.app N = (counitIso R k).hom.app N :=
  SemimoduleCat.hom_ext (coordinateReconstruction_coordinateChange R I k l)

/-- Coefficient recovery is compatible with the natural change of coordinate functor. -/
lemma coefficientIso_coordinateChange (k l : I) (M : SemimoduleCat.{max uI v} R) :
    (coordinateChangeIso R k l).hom.app ((SemimoduleCat.toMatrixModCat R I).obj M) ≫
        (coefficientIso R l).hom.app M = (coefficientIso R k).hom.app M :=
  SemimoduleCat.hom_ext (coefficientEquiv_coordinateChange R I M k l)

/-- The coordinate-range triangle for the specified unit and counit. -/
lemma coordinate_triangle (k : I) (N : SemimoduleCat.{max uI v} (Matrix I I R)) :
    (coefficientIso R k).inv.app ((toSemimoduleCat R k).obj N) ≫
        (toSemimoduleCat R k).map ((counitIso R k).hom.app N) = 𝟙 _ :=
  SemimoduleCat.hom_ext (coordinateMap_coordinateReconstruction_triangle R I k)

end MatrixSemimoduleCat

namespace SemimoduleCat

variable {I}

/-- Semimodules over a semiring and its finite nonempty matrix semiring are equivalent.
The unit is inverse coefficient recovery and the counit is coordinate reconstruction. -/
def matrixEquivalence (k : I) : SemimoduleCat.{max uI v} R ≌
    SemimoduleCat.{max uI v} (Matrix I I R) where
  functor := toMatrixModCat R I
  inverse := MatrixSemimoduleCat.toSemimoduleCat R k
  unitIso := (MatrixSemimoduleCat.coefficientIso R k).symm
  counitIso := MatrixSemimoduleCat.counitIso R k
  functor_unitIso_comp M := SemimoduleCat.hom_ext
    (Matrix.Module.coordinateReconstruction_triangle R I (M := M) k)

@[simp]
lemma matrixEquivalence_functor (k : I) :
    (matrixEquivalence R k).functor = toMatrixModCat R I := rfl

@[simp]
lemma matrixEquivalence_inverse (k : I) :
    (matrixEquivalence R k).inverse = MatrixSemimoduleCat.toSemimoduleCat R k := rfl

@[simp]
lemma matrixEquivalence_unitIso (k : I) :
    (matrixEquivalence R k).unitIso = (MatrixSemimoduleCat.coefficientIso R k).symm := rfl

@[simp]
lemma matrixEquivalence_counitIso (k : I) :
    (matrixEquivalence R k).counitIso = MatrixSemimoduleCat.counitIso R k := rfl

end SemimoduleCat

end Semiring

section Ring

variable {R : Type uR} {I : Type uI} [Ring R] [Fintype I] [DecidableEq I]

local notation "J_R" =>
  CategoryTheory.Equivalence.functor (ModuleCat.equivalenceSemimoduleCat (R := R))
local notation "J_S" =>
  CategoryTheory.Equivalence.functor (ModuleCat.equivalenceSemimoduleCat (R := Matrix I I R))

namespace SemimoduleCat

private lemma transportLinearMap_apply {S X Y : Type*} [Semiring S]
    [AddCommMonoid X] [AddCommMonoid Y]
    {m₁ m₂ : Module S X} {n₁ n₂ : Module S Y} (hm : m₁ = m₂) (hn : n₁ = n₂)
    (f : @LinearMap S S _ _ (RingHom.id S) X Y _ _ m₁ n₁) (x : X) :
    (Eq.mp (congrArg₂ (fun m n => @LinearMap S S _ _ (RingHom.id S) X Y _ _ m n)
      hm hn) f) x = f x := by
  cases hm
  cases hn
  rfl

/-- Over a ring, the semiring column functor agrees naturally with the existing ring
column functor through the forward functors of `ModuleCat.equivalenceSemimoduleCat`.
The components are identity on vectors, with the two column actions compared explicitly. -/
def toMatrixModCatRingIso :
    (J_R : ModuleCat.{max uI v} R ⥤ SemimoduleCat.{max uI v} R) ⋙
        SemimoduleCat.toMatrixModCat R I ≅ ModuleCat.toMatrixModCat R I ⋙ J_S :=
  NatIso.ofComponents (fun M =>
    (show (SemimoduleCat.toMatrixModCat R I).obj ((J_R).obj M) ≃ₗ[Matrix I I R]
        (J_S).obj ((ModuleCat.toMatrixModCat R I).obj M) from
      { __ := AddEquiv.refl (I → M)
        map_smul' A x := congrArg
          (fun h : Module (Matrix I I R) (I → M) =>
            @SMul.smul (Matrix I I R) (I → M)
              h.toDistribMulAction.toMulAction.toSemigroupAction.toSMul A x)
          (Matrix.Module.matrixModuleSemiring_eq_matrixModule
            (I := I) (R := R) (M := M)) }).toModuleIsoₛ) (fun {M M'} f => by
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro x
    change LinearMap.matrixModuleMap I f.hom x = LinearMap.mapMatrixModule I f.hom x
    exact (transportLinearMap_apply
      (Matrix.Module.matrixModuleSemiring_eq_matrixModule (I := I) (R := R) (M := M))
      (Matrix.Module.matrixModuleSemiring_eq_matrixModule (I := I) (R := R) (M := M'))
      (LinearMap.matrixModuleMap I f.hom) x).symm.trans
        (DFunLike.congr_fun (LinearMap.matrixModuleMap_eq_mapMatrixModule I f.hom) x))

/-- The ring comparison of column functors is identity on vectors. -/
lemma toMatrixModCatRingIso_hom_app_apply
    (M : ModuleCat.{max uI v} R) (x : I → M) :
    (toMatrixModCatRingIso (R := R) (I := I)).hom.app M x = x := rfl

/-- The inverse ring comparison of column functors is identity on vectors. -/
lemma toMatrixModCatRingIso_inv_app_apply
    (M : ModuleCat.{max uI v} R) (x : I → M) :
    (toMatrixModCatRingIso (R := R) (I := I)).inv.app M x = x := rfl

end SemimoduleCat

namespace MatrixSemimoduleCat

private lemma transportLinearEquiv_apply {S X Y : Type*} [Semiring S]
    [AddCommMonoid X] [AddCommMonoid Y] [Module S Y]
    {m₁ m₂ : Module S X} (hm : m₁ = m₂)
    (e : letI : Module S X := m₁; X ≃ₗ[S] Y) (x : X) :
    (Eq.mp (congrArg (fun m : Module S X => letI : Module S X := m; X ≃ₗ[S] Y) hm) e) x =
      e x := by
  cases hm
  rfl

/-- Over a ring, the coordinate functor agrees naturally with Mathlib's existing range
functor. The components preserve the ambient representatives and inherited scalar actions. -/
def toSemimoduleCatRingIso (k : I) :
    (J_S : ModuleCat.{max uI v} (Matrix I I R) ⥤
        SemimoduleCat.{max uI v} (Matrix I I R)) ⋙ toSemimoduleCat R k ≅
      MatrixModCat.toModuleCat R k ⋙ J_R :=
  NatIso.ofComponents (fun N =>
    (show (toSemimoduleCat R k).obj ((J_S).obj N) ≃ₗ[R]
        (J_R).obj ((MatrixModCat.toModuleCat R k).obj N) from by
      letI : Module R N := Module.compHom N (Matrix.scalar I)
      letI := MatrixModCat.isScalarTower_toModuleCat R N
      change Matrix.Module.coordinateSubmodule R I N k ≃ₗ[R]
        MatrixModCat.toModuleCatObj R N k
      have h := Matrix.Module.coordinateSubmodule_eq_toModuleCatObj
        (R := R) (I := I) (N := N) k
      exact
        { toFun := fun x => ⟨x.1, by rw [← h]; exact x.2⟩
          invFun := fun x => ⟨x.1, by rw [h]; exact x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }).toModuleIsoₛ) (fun {N N'} f => by
    let : Module R N := Module.compHom N (Matrix.scalar I)
    let : Module R N' := Module.compHom N' (Matrix.scalar I)
    apply SemimoduleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact Matrix.Module.coordinateMap_apply_eq_fromMatrixLinear (N := N) (N' := N') R I
      (MatrixModCat.isScalarTower_toModuleCat R N)
      (MatrixModCat.isScalarTower_toModuleCat R N') k f.hom x)

/-- The ring comparison of coordinate functors preserves range representatives. -/
lemma coe_toSemimoduleCatRingIso_hom_app_apply (k : I)
    (N : ModuleCat.{max uI v} (Matrix I I R))
    (x : Matrix.Module.coordinateSubmodule R I N k) :
    Subtype.val ((toSemimoduleCatRingIso (R := R) k).hom.app N x :
      Matrix.Module.coordinateSubmodule R I N k) = (x : N) := rfl

/-- The inverse ring comparison of coordinate functors preserves range representatives. -/
lemma coe_toSemimoduleCatRingIso_inv_app_apply (k : I)
    (N : ModuleCat.{max uI v} (Matrix I I R))
    (x : Matrix.Module.coordinateSubmodule R I N k) :
    Subtype.val ((toSemimoduleCatRingIso (R := R) k).inv.app N x :
      Matrix.Module.coordinateSubmodule R I N k) = (x : N) := rfl

/-- Natural coefficient recovery agrees with the old ring unit component, whose forward
map is sum recovery. The equivalence `ModuleCat.matrixEquivalence` uses its inverse as unit. -/
lemma coefficientIso_ring (k : I) (M : ModuleCat.{max uI v} R) :
    (coefficientIso R k).hom.app ((J_R).obj M) =
      (toSemimoduleCat R k).map
          ((SemimoduleCat.toMatrixModCatRingIso (R := R) (I := I)).hom.app M) ≫
        (toSemimoduleCatRingIso (R := R) k).hom.app ((ModuleCat.toMatrixModCat R I).obj M) ≫
        (J_R).map ((MatrixModCat.unitIso R k).hom.app M) := by
  apply SemimoduleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Matrix.Module.coefficientEquiv_apply_eq_fromModuleCatToModuleCatLinearEquiv
    (R := R) (I := I) (M := M) k x

/-- Natural reconstruction agrees with the old ring counit component after the natural
range and column comparisons. No inverse of the ring-to-semimodule bridge is used. -/
lemma counitIso_ring (k : I)
    (N : ModuleCat.{max uI v} (Matrix I I R)) :
    (counitIso R k).hom.app ((J_S).obj N) =
      (SemimoduleCat.toMatrixModCat R I).map
          ((toSemimoduleCatRingIso (R := R) k).hom.app N) ≫
        (SemimoduleCat.toMatrixModCatRingIso (R := R) (I := I)).hom.app
          ((MatrixModCat.toModuleCat R k).obj N) ≫
        (J_S).map ((MatrixModCat.counitIso R k).hom.app N) := by
  apply SemimoduleCat.hom_ext
  apply LinearMap.ext
  intro x
  change Matrix.Module.coordinateReconstruction R I N k x =
    (toModuleCatFromModuleCatLinearEquiv R N k).symm x
  exact (transportLinearEquiv_apply
    (Matrix.Module.matrixModuleSemiring_eq_matrixModule
      (I := I) (R := R) (M := Matrix.Module.coordinateSubmodule R I N k))
    (Matrix.Module.coordinateReconstruction R I N k) x).symm.trans
      (DFunLike.congr_fun
        (Matrix.Module.coordinateReconstruction_eq_toModuleCatFromModuleCatLinearEquiv N k) x)

end MatrixSemimoduleCat

end Ring
