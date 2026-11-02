/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

Portions adapted from Mathlib/RingTheory/Morita/Matrix.lean:
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import CoherentModules.LinearAlgebra.Matrix.Module
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.RingTheory.Morita.Matrix

/-!
# Reconstruction from a matrix coordinate summand

A module over a finite matrix semiring is reconstructed from the range of a diagonal
matrix unit. Its coefficient action is restriction along `Matrix.scalar`; no additional
coefficient action is supplied. The coordinate summand is a linear-map range, with the
usual submodule inclusion and projection API.

On columns, coefficient recovery is the sum of coordinates, through the identity
comparison between restricted and pointwise scalars. On the coordinate range this sum
is evaluation at the chosen index.

The raw constructions generalize the ring constructions in Mathlib's
`RingTheory.Morita.Matrix`, by Yunzhou Xie and Jujian Zhang. The bundled ring equivalence
is not reconstructed here.
-/

@[expose] public section

universe uR uI uN uM

namespace Matrix.Module

open Matrix
open scoped Matrix.Module

variable {R : Type uR} {I : Type uI} {N : Type uN}
  [r : Semiring R] [Fintype I] [DecidableEq I]
  [aN : AddCommMonoid N] [hSN : Module (Matrix I I R) N]

section Compatible

variable [hRN : Module R N]
  (h : ∀ (a : R) (x : N), a • x = scalar I a • x)

/-- A matrix unit is coefficient-linear whenever coefficient scalars act by scalar matrices. -/
def matrixUnitLinearMapOfScalar (i j : I) : N →ₗ[R] N where
  __ := DistribSMul.toAddMonoidHom N (single i j (1 : R) : Matrix I I R)
  map_smul' a x := by
    have hc : Commute (single i j (1 : R)) (scalar I a) := by
      ext s t
      simp [scalar_apply, diagonal_mul, mul_diagonal, single]
    change single i j (1 : R) • (a • x) = a • (single i j (1 : R) • x)
    rw [h, h, ← mul_smul, ← mul_smul, hc.eq]

/-- Applying the coefficient-linear matrix unit is its given matrix action. -/
@[simp]
lemma matrixUnitLinearMapOfScalar_apply (i j : I) (x : N) :
    matrixUnitLinearMapOfScalar h i j x = single i j (1 : R) • x := rfl

/-- The coordinate range with a compatible coefficient action. -/
def coordinateSubmoduleOfScalar (k : I) : Submodule R N :=
  (matrixUnitLinearMapOfScalar h k k).range

/-- Membership in the coordinate range is membership in the image of the matrix unit. -/
lemma mem_coordinateSubmoduleOfScalar (k : I) (x : N) :
    x ∈ coordinateSubmoduleOfScalar h k ↔ ∃ y, single k k (1 : R) • y = x := Iff.rfl

end Compatible

variable (R I N)

local notation "DMod" => Module.compHom N (scalar (α := R) I)
local notation "RowsR" => @Pi.module I (fun _ : I => R) R r
  (fun _ => inferInstance) (fun _ => @Semiring.toModule R r)
local notation "MatricesR" => @Pi.module I (fun _ : I => I → R) R r
  (fun _ => inferInstance) (fun _ => RowsR)

/-- The restricted coefficient action forms a tower with entrywise regular matrix scalars. -/
lemma restricted_isScalarTower :
    letI : Module R (Matrix I I R) := MatricesR
    letI : Module R N := DMod
    IsScalarTower R (Matrix I I R) N := by
  let : Module R (Matrix I I R) := MatricesR
  let : Module R N := DMod
  exact ⟨fun a A x => by
    change (a • A) • x = scalar I a • (A • x)
    rw [← mul_smul, scalar_apply, smul_eq_diagonal_mul]⟩

/-- A tower with regular entrywise matrix scalars forces restriction along scalar matrices. -/
lemma smul_eq_scalar_smul_of_tower [hRN : Module R N]
    (hT : letI : Module R (Matrix I I R) := MatricesR
      IsScalarTower R (Matrix I I R) N)
    (a : R) (x : N) : a • x = scalar I a • x := by
  let : Module R (Matrix I I R) := MatricesR
  let : IsScalarTower R (Matrix I I R) N := hT
  calc
    a • x = (a • (1 : Matrix I I R)) • x := by rw [smul_assoc, one_smul]
    _ = scalar I a • x := by rw [smul_one_eq_diagonal]; rfl

/-- Restriction of the given matrix action along scalar matrices. -/
@[simp]
lemma restricted_smul (a : R) (x : N) :
    letI : Module R N := DMod
    a • x = scalar I a • x := rfl

/-- A matrix unit acting linearly for the coefficient action restricted along scalar matrices. -/
def matrixUnitLinearMap (i j : I) :
    @LinearMap R R r r (RingHom.id R) N N aN aN DMod DMod :=
  @matrixUnitLinearMapOfScalar R I N r _ _ aN hSN DMod (fun _ _ => rfl) i j

/-- A matrix unit acts by the original matrix-module action. -/
@[simp]
lemma matrixUnitLinearMap_apply (i j : I) (x : N) :
    matrixUnitLinearMap R I N i j x = single i j (1 : R) • x := rfl

/-- The coefficient summand is exactly the range of the diagonal matrix unit. -/
def coordinateSubmodule (k : I) : @Submodule R N r aN DMod := by
  letI : Module R N := DMod
  exact (matrixUnitLinearMap R I N k k).range

/-- The diagonal matrix-unit operator is idempotent. -/
lemma matrixUnitLinearMap_idempotent (k : I) :
    letI : Module R N := DMod
    IsIdempotentElem (matrixUnitLinearMap R I N k k) := by
  let : Module R N := DMod
  ext x
  simp [Module.End.mul_apply, ← mul_smul]

/-- The diagonal matrix unit projects onto its coordinate range. -/
lemma coordinateSubmodule_isProj (k : I) :
    letI : Module R N := DMod
    LinearMap.IsProj (coordinateSubmodule R I N k) (matrixUnitLinearMap R I N k k) := by
  let : Module R N := DMod
  exact LinearMap.IsIdempotentElem.isProj_range _ (matrixUnitLinearMap_idempotent R I N k)

/-- A vector belongs to the coordinate range precisely when the diagonal matrix unit fixes it. -/
@[simp]
lemma mem_coordinateSubmodule (k : I) (x : N) :
    x ∈ coordinateSubmodule R I N k ↔ single k k (1 : R) • x = x := by
  let : Module R N := DMod
  exact LinearMap.IsIdempotentElem.mem_range_iff (matrixUnitLinearMap_idempotent R I N k)

/-- The coordinate retraction, obtained by restricting the codomain of the projector. -/
def coordinateProjection (k : I) :
    letI : Module R N := DMod
    N →ₗ[R] coordinateSubmodule R I N k := by
  letI : Module R N := DMod
  exact (coordinateSubmodule_isProj R I N k).codRestrict

/-- The coordinate retraction has the diagonal matrix-unit representative. -/
@[simp]
lemma coe_coordinateProjection (k : I) (x : N) :
    (coordinateProjection R I N k x : N) = single k k (1 : R) • x := rfl

/-- The coordinate retraction fixes the coordinate summand. -/
@[simp]
lemma coordinateProjection_coe (k : I) (x : coordinateSubmodule R I N k) :
    coordinateProjection R I N k (x : N) = x := by
  let : Module R N := DMod
  exact (coordinateSubmodule_isProj R I N k).codRestrict_apply_cod x

/-- Inclusion after coordinate retraction is the diagonal matrix-unit operator. -/
lemma subtype_comp_coordinateProjection (k : I) :
    letI : Module R N := DMod
    (coordinateSubmodule R I N k).subtype.comp (coordinateProjection R I N k) =
      matrixUnitLinearMap R I N k k := by
  let : Module R N := DMod
  exact (coordinateSubmodule_isProj R I N k).subtype_comp_codRestrict

/-- Retraction after inclusion is the identity. -/
@[simp]
lemma coordinateProjection_comp_subtype (k : I) :
    letI : Module R N := DMod
    (coordinateProjection R I N k).comp (coordinateSubmodule R I N k).subtype =
      LinearMap.id := by
  let : Module R N := DMod
  apply LinearMap.ext
  intro x
  exact coordinateProjection_coe R I N k x

/-- A map fixed by the projector factors through the coordinate range by codomain restriction. -/
lemma range_le_coordinateSubmodule {X : Type*} [AddCommMonoid X] [Module R X]
    (k : I) (g : letI : Module R N := DMod; X →ₗ[R] N) :
    letI : Module R N := DMod
    (matrixUnitLinearMap R I N k k).comp g = g ↔ g.range ≤ coordinateSubmodule R I N k := by
  let : Module R N := DMod
  exact LinearMap.IsIdempotentElem.comp_eq_right_iff
    (matrixUnitLinearMap_idempotent R I N k) g

/-- Identity comparison of the coordinate range with any compatible coefficient action. -/
def coordinateSubmoduleEquivOfScalar [hRN : Module R N]
    (h : ∀ (a : R) (x : N), a • x = scalar I a • x) (k : I) :
    coordinateSubmodule R I N k ≃ₗ[R] coordinateSubmoduleOfScalar h k where
  __ := AddEquiv.refl _
  map_smul' a x := Subtype.ext <| (h a (x : N)).symm

/-- The compatible-scalar comparison is identity on representatives. -/
@[simp]
lemma coe_coordinateSubmoduleEquivOfScalar_apply [hRN : Module R N]
    (h : ∀ (a : R) (x : N), a • x = scalar I a • x) (k : I)
    (x : coordinateSubmodule R I N k) :
    (coordinateSubmoduleEquivOfScalar R I N h k x : N) = x := rfl

/-- The inverse compatible-scalar comparison is identity on representatives. -/
@[simp]
lemma coe_coordinateSubmoduleEquivOfScalar_symm_apply [hRN : Module R N]
    (h : ∀ (a : R) (x : N), a • x = scalar I a • x) (k : I)
    (x : coordinateSubmoduleOfScalar h k) :
    ((coordinateSubmoduleEquivOfScalar R I N h k).symm x : N) = x := rfl

/-- Coordinates in the chosen summand reconstruct the original matrix module. -/
def coordinateReconstruction (k : I) : (I → coordinateSubmodule R I N k) ≃ₗ[Matrix I I R] N :=
  letI : Module R N := DMod
  LinearEquiv.symm
    { toFun := fun x i => ⟨single k i (1 : R) • x,
        (mem_coordinateSubmodule R I N k _).2 (by simp [← mul_smul])⟩
      map_add' := fun _ _ => by ext; simp
      map_smul' := fun A x => funext fun i => Subtype.ext <| by
        have hs : single k i (1 : R) * A =
            ∑ j, scalar I (A i j) * single k j (1 : R) := by
          ext s t
          simp only [scalar_apply, diagonal_mul, Matrix.sum_apply]
          by_cases hk : k = s <;> simp [mul_apply, single, hk]
        simp only [RingHom.id_apply, smul_apply_semiring,
          AddSubmonoidClass.coe_finsetSum, SetLike.val_smul,
          restricted_smul R I N, ← mul_smul, ← Finset.sum_smul]
        exact congrArg (fun B : Matrix I I R => B • x) hs
      invFun := fun v => ∑ i, single i k (1 : R) • (v i : N)
      left_inv := fun x => by simp [← mul_smul, ← Finset.sum_smul, sum_single_one]
      right_inv := fun v => by
        ext i
        simp only [Finset.smul_sum]
        rw [Finset.sum_eq_single i (fun b _ hb => by
          simp [← mul_smul, single_mul_single_of_ne _ _ _ _ hb.symm]) (by simp)]
        simpa [← mul_smul] using (mem_coordinateSubmodule R I N k (v i : N)).1 (v i).2 }

/-- Reconstruction sums the translated coordinate representatives. -/
lemma coordinateReconstruction_apply (k : I) (v : I → coordinateSubmodule R I N k) :
    coordinateReconstruction R I N k v = ∑ i, single i k (1 : R) • (v i : N) := rfl

/-- The inverse reconstruction takes the matrix-unit coordinates. -/
@[simp]
lemma coe_coordinateReconstruction_symm_apply (k : I) (x : N) (i : I) :
    ((coordinateReconstruction R I N k).symm x i : N) = single k i (1 : R) • x := rfl

end Matrix.Module

namespace Matrix.Module

open Matrix
open scoped Matrix.Module

variable {R : Type uR} {I : Type uI} {M : Type uM}
  [r : Semiring R] [Fintype I] [DecidableEq I]
  [aM : AddCommMonoid M] [hM : Module R M]

local notation "PMod" => @Pi.module I (fun _ : I => M) R r (fun _ => aM) (fun _ => hM)
local notation "CMod" => @matrixModuleSemiring I R M r _ _ aM hM

variable (R I M) (k : I)

local notation "PRange" => @coordinateSubmoduleOfScalar R I (I → M) r _ _ _ CMod PMod
  (fun a x => Eq.symm (scalar_smul_semiring a x)) k

/-- The identity comparison on the coordinate range, from restricted to pointwise scalars. -/
def columnCoordinateEquiv : coordinateSubmodule R I (I → M) k ≃ₗ[R] PRange :=
  @coordinateSubmoduleEquivOfScalar R I (I → M) r _ _ _ CMod PMod
    (fun a x => Eq.symm (scalar_smul_semiring a x)) k

/-- The scalar comparison does not change coordinate representatives. -/
@[simp]
lemma coe_columnCoordinateEquiv_apply (x : coordinateSubmodule R I (I → M) k) :
    (columnCoordinateEquiv R I M k x : I → M) = x := rfl

/-- The inverse scalar comparison does not change coordinate representatives. -/
@[simp]
lemma coe_columnCoordinateEquiv_symm_apply (x : PRange) :
    ((columnCoordinateEquiv R I M k).symm x : I → M) = x := rfl

/-- Sum recovery on the coordinate range with pointwise coefficient scalars. -/
def coordinateSumEquiv : PRange ≃ₗ[R] M where
  toFun x := ∑ j, x.1 j
  map_add' := fun _ _ => by simp [Finset.sum_add_distrib]
  map_smul' := fun a x => by simp [Finset.smul_sum]
  invFun x := ⟨Pi.single k x,
    (mem_coordinateSubmoduleOfScalar _ k _).2 ⟨Function.const I x, by simp⟩⟩
  left_inv := fun ⟨x, hx⟩ => by
    obtain ⟨y, hy⟩ := (mem_coordinateSubmoduleOfScalar _ k x).1 hx
    rw [single_smul_semiring, one_smul] at hy
    apply Subtype.ext
    simp [← hy]
  right_inv := fun x => by simp

/-- The sum-recovery representative is the sum of coordinates. -/
lemma coordinateSumEquiv_apply (x : PRange) :
    coordinateSumEquiv R I M k x = ∑ j, (x : I → M) j := rfl

/-- Inverse sum recovery is the supported vector at the chosen index. -/
@[simp]
lemma coe_coordinateSumEquiv_symm_apply (x : M) :
    ((coordinateSumEquiv R I M k).symm x : I → M) = Pi.single k x := rfl

/-- A column belongs to the coordinate range exactly when it is supported at that coordinate. -/
lemma mem_coordinateSubmodule_columns (x : I → M) :
    x ∈ coordinateSubmodule R I (I → M) k ↔ x = Pi.single k (x k) := by
  rw [mem_coordinateSubmodule]
  simp only [single_smul_semiring, one_smul, eq_comm]

/-- A vector supported at the chosen coordinate belongs to its coordinate range. -/
lemma single_mem_coordinateSubmodule (x : M) :
    Pi.single k x ∈ coordinateSubmodule R I (I → M) k := by
  rw [mem_coordinateSubmodule_columns]
  simp

/-- Every other coordinate of a vector in the coordinate range vanishes. -/
lemma coordinateSubmodule_apply_eq_zero (x : coordinateSubmodule R I (I → M) k)
    {j : I} (hj : j ≠ k) : (x : I → M) j = 0 := by
  have hs := (mem_coordinateSubmodule_columns R I M k (x : I → M)).1 x.2
  exact (congrFun hs j).trans (by simp [hj])

/-- On the coordinate range the sum of coordinates is evaluation at the chosen index. -/
lemma sum_coordinateSubmodule (x : coordinateSubmodule R I (I → M) k) :
    ∑ j, (x : I → M) j = (x : I → M) k := by
  have hs := (mem_coordinateSubmodule_columns R I M k (x : I → M)).1 x.2
  simpa using congrArg (fun y : I → M => ∑ j, y j) hs

/-- Recover coefficients by the identity scalar comparison followed by sum recovery. -/
def coefficientEquiv : coordinateSubmodule R I (I → M) k ≃ₗ[R] M :=
  (columnCoordinateEquiv R I M k).trans (coordinateSumEquiv R I M k)

/-- Coefficient recovery is evaluation at the chosen coordinate. -/
@[simp]
lemma coefficientEquiv_apply (x : coordinateSubmodule R I (I → M) k) :
    coefficientEquiv R I M k x = (x : I → M) k :=
  sum_coordinateSubmodule R I M k x

/-- The inverse coefficient equivalence is the supported-vector inclusion. -/
@[simp]
lemma coe_coefficientEquiv_symm_apply (x : M) :
    ((coefficientEquiv R I M k).symm x : I → M) = Pi.single k x := rfl

end Matrix.Module

namespace Matrix.Module

open Matrix
open scoped Matrix.Module

section Ring

variable {R : Type uR} {I : Type uI} {N : Type uN}
  [Ring R] [Fintype I] [DecidableEq I] [AddCommGroup N]
  [Module (Matrix I I R) N]

local notation "RowsR" => @Pi.module I (fun _ : I => R) R _
  (fun _ => inferInstance) (fun _ => @Semiring.toModule R inferInstance)
local notation "MatricesR" => @Pi.module I (fun _ : I => I → R) R _
  (fun _ => inferInstance) (fun _ => RowsR)

/-- With the old scalar-tower hypotheses, the generalized range is Mathlib's coordinate object. -/
lemma coordinateSubmoduleOfScalar_eq_toModuleCatObj [Module R N]
    (hT : letI : Module R (Matrix I I R) := MatricesR
      IsScalarTower R (Matrix I I R) N)
    (h : ∀ (a : R) (x : N), a • x = scalar I a • x) (k : I) :
    letI : Module R (Matrix I I R) := MatricesR
    letI : IsScalarTower R (Matrix I I R) N := hT
    coordinateSubmoduleOfScalar h k = MatrixModCat.toModuleCatObj R N k := by
  let : Module R (Matrix I I R) := MatricesR
  let : IsScalarTower R (Matrix I I R) N := hT
  ext x
  rfl

/-- The canonical coordinate range agrees with Mathlib's range for the diagonal restriction. -/
lemma coordinateSubmodule_eq_toModuleCatObj (k : I) :
    letI : Module R (Matrix I I R) := MatricesR
    letI : Module R N := Module.compHom N (scalar (α := R) I)
    letI : IsScalarTower R (Matrix I I R) N := restricted_isScalarTower R I N
    coordinateSubmodule R I N k = MatrixModCat.toModuleCatObj R N k := by
  let : Module R (Matrix I I R) := MatricesR
  let : Module R N := Module.compHom N (scalar (α := R) I)
  let : IsScalarTower R (Matrix I I R) N := restricted_isScalarTower R I N
  ext x
  rfl

private theorem transportEquiv_apply {S X Y : Type*} [Semiring S]
    [AddCommMonoid X] [AddCommMonoid Y] [Module S Y]
    {m₁ m₂ : Module S X} (hm : m₁ = m₂)
    (e : letI : Module S X := m₁; X ≃ₗ[S] Y) (x : X) :
    (Eq.mp (congrArg (fun m : Module S X => letI : Module S X := m; X ≃ₗ[S] Y) hm) e) x =
      e x := by
  cases hm
  rfl

/-- Reconstruction agrees with the symmetric orientation of Mathlib's ring equivalence,
after the equality of the column-module data. -/
lemma coordinateReconstruction_eq_toModuleCatFromModuleCatLinearEquiv
    (M : ModuleCat (Matrix I I R)) (k : I) :
    Eq.mp (congrArg
      (fun h : Module (Matrix I I R) (I → coordinateSubmodule R I M k) =>
        letI : Module (Matrix I I R) (I → coordinateSubmodule R I M k) := h
        (I → coordinateSubmodule R I M k) ≃ₗ[Matrix I I R] M)
      (matrixModuleSemiring_eq_matrixModule
        (I := I) (R := R) (M := coordinateSubmodule R I M k)))
      (coordinateReconstruction R I M k) =
        (toModuleCatFromModuleCatLinearEquiv R M k).symm := by
  apply LinearEquiv.ext
  intro v
  rw [transportEquiv_apply (matrixModuleSemiring_eq_matrixModule
    (I := I) (R := R) (M := coordinateSubmodule R I M k))]
  rfl

variable {M : Type uM} [AddCommGroup M] [Module R M]

/-- The identity scalar comparison has the same representatives as Mathlib's ring bridge. -/
lemma columnCoordinateEquiv_apply_eq_fromModuleCatToModuleCatLinearEquivtoModuleCatObj
    (k : I) (x : coordinateSubmodule R I (I → M) k) :
    (columnCoordinateEquiv R I M k x : I → M) =
      (fromModuleCatToModuleCatLinearEquivtoModuleCatObj R M k x : I → M) := rfl

/-- Coefficient recovery agrees with Mathlib's identity bridge followed by its sum equivalence. -/
lemma coefficientEquiv_apply_eq_fromModuleCatToModuleCatLinearEquiv
    (k : I) (x : coordinateSubmodule R I (I → M) k) :
    coefficientEquiv R I M k x =
      fromModuleCatToModuleCatLinearEquiv R M k
        (fromModuleCatToModuleCatLinearEquivtoModuleCatObj R M k x) := by
  rw [coefficientEquiv_apply]
  exact (sum_coordinateSubmodule R I M k x).symm

/-- Inverse coefficient recovery agrees on representatives with the inverse ring composition. -/
lemma coe_coefficientEquiv_symm_eq_fromModuleCatToModuleCatLinearEquiv
    (k : I) (x : M) :
    ((coefficientEquiv R I M k).symm x : I → M) =
      Subtype.val ((fromModuleCatToModuleCatLinearEquivtoModuleCatObj R M k).symm
        ((fromModuleCatToModuleCatLinearEquiv R M k).symm x)) := rfl

end Ring

end Matrix.Module
