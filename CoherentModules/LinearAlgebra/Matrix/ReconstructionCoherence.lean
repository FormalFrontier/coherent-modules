/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

Portions adapted from Mathlib/RingTheory/Morita/Matrix.lean:
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
module

public import CoherentModules.LinearAlgebra.Matrix.Reconstruction

/-!
# Coherence of matrix coordinate reconstruction

The coordinate range construction is additive on matrix-linear maps. Reconstruction and
coefficient recovery are natural, and satisfy the two component identities and triangle
identities. Changing the chosen coordinate gives compatible coefficient-linear equivalences.

Every coefficient action on an arbitrary matrix module is restriction along `Matrix.scalar`.
In particular, no second coefficient action or scalar-tower hypothesis is needed. The range
maps are coefficient-linear, not in general matrix-linear. All arguments use only semiring
and additive commutative monoid operations.

## References

The restriction on morphisms generalizes `MatrixModCat.fromMatrixLinear` in Mathlib's
`RingTheory.Morita.Matrix`, by Yunzhou Xie and Jujian Zhang. Its ring specialization is
compared through the identity scalar and range bridges; no categorical ring equivalence is
reconstructed here.
-/

@[expose] public section

universe uR uI uN uN' uN'' uM uM'

namespace Matrix.Module

open Matrix
open scoped Matrix.Module

section Morphisms

variable {R : Type uR} {I : Type uI}
  [Semiring R] [Fintype I] [DecidableEq I]
  {N : Type uN} {N' : Type uN'} {N'' : Type uN''}
  [AddCommMonoid N] [AddCommMonoid N'] [AddCommMonoid N'']
  [Module (Matrix I I R) N] [Module (Matrix I I R) N'] [Module (Matrix I I R) N'']

variable (R I N N')

/-- Matrix-linear maps preserve both coefficient actions restricted along scalar matrices. -/
lemma restricted_compatibleSMul :
    letI : Module R N := Module.compHom N (scalar (α := R) I)
    letI : Module R N' := Module.compHom N' (scalar (α := R) I)
    LinearMap.CompatibleSMul N N' R (Matrix I I R) := by
  let : Module R N := Module.compHom N (scalar (α := R) I)
  let : Module R N' := Module.compHom N' (scalar (α := R) I)
  exact ⟨fun f a x => f.map_smul (scalar I a) x⟩

variable {N N'}

/-- The additive assignment on coordinate ranges, obtained by scalar and image restriction. -/
def coordinateMap (k : I) :
    (N →ₗ[Matrix I I R] N') →+
      (coordinateSubmodule R I N k →ₗ[R] coordinateSubmodule R I N' k) where
  toFun f := by
    letI : Module R N := Module.compHom N (scalar (α := R) I)
    letI : Module R N' := Module.compHom N' (scalar (α := R) I)
    letI := restricted_compatibleSMul R I N N'
    exact (f.restrictScalars R).restrict fun x hx => by
      rw [mem_coordinateSubmodule] at hx ⊢
      change single k k (1 : R) • f x = f x
      rw [← f.map_smul, hx]
  map_zero' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl
  map_add' f g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rfl

/-- On representatives the coordinate-range map is the original matrix-linear map. -/
@[simp]
lemma coe_coordinateMap_apply (k : I) (f : N →ₗ[Matrix I I R] N')
    (x : coordinateSubmodule R I N k) :
    (coordinateMap R I k f x : N') = f (x : N) := rfl

/-- Coordinate-range restriction preserves identity maps. -/
@[simp]
lemma coordinateMap_id (k : I) :
    coordinateMap R I k (LinearMap.id : N →ₗ[Matrix I I R] N) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- Coordinate-range restriction preserves composition. -/
lemma coordinateMap_comp (k : I) (f : N →ₗ[Matrix I I R] N')
    (g : N' →ₗ[Matrix I I R] N'') :
    coordinateMap R I k (g.comp f) =
      (coordinateMap R I k g).comp (coordinateMap R I k f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  rfl

/-- Reconstruction is natural in arbitrary matrix-linear maps. -/
lemma coordinateReconstruction_naturality (k : I) (f : N →ₗ[Matrix I I R] N') :
    f.comp (coordinateReconstruction R I N k).toLinearMap =
      (coordinateReconstruction R I N' k).toLinearMap.comp
        (LinearMap.matrixModuleMap I (coordinateMap R I k f)) := by
  apply LinearMap.ext
  intro v
  simp [coordinateReconstruction_apply]

/-- Reconstruction of a vector supported at the chosen coordinate is its representative. -/
@[simp]
lemma coordinateReconstruction_single (k : I) (x : coordinateSubmodule R I N k) :
    coordinateReconstruction R I N k (Pi.single k x) = (x : N) := by
  have hx := (mem_coordinateSubmodule R I N k (x : N)).1 x.2
  rw [coordinateReconstruction_apply, Finset.sum_eq_single k]
  · simpa using hx
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- Restricting reconstruction to its coordinate range is coefficient recovery. -/
lemma coordinateMap_coordinateReconstruction (k : I) :
    coordinateMap R I k (coordinateReconstruction R I N k).toLinearMap =
      (coefficientEquiv R I (coordinateSubmodule R I N k) k).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [coe_coordinateMap_apply, LinearEquiv.coe_coe, coefficientEquiv_apply]
  have hx := (mem_coordinateSubmodule_columns R I
    (coordinateSubmodule R I N k) k (x : I → coordinateSubmodule R I N k)).1 x.2
  rw [hx, coordinateReconstruction_single]
  simp

/-- The coordinate-range triangle identity, without subtraction or cancellation. -/
lemma coordinateMap_coordinateReconstruction_triangle (k : I) :
    (coordinateMap R I k (coordinateReconstruction R I N k).toLinearMap).comp
        (coefficientEquiv R I (coordinateSubmodule R I N k) k).symm.toLinearMap =
      LinearMap.id := by
  rw [coordinateMap_coordinateReconstruction]
  apply LinearMap.ext
  intro x
  exact (coefficientEquiv R I (coordinateSubmodule R I N k) k).apply_symm_apply x

end Morphisms

section Columns

variable {R : Type uR} {I : Type uI}
  [Semiring R] [Fintype I] [DecidableEq I]
  {M : Type uM} {M' : Type uM'}
  [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M']

variable (R I)

/-- Coefficient recovery is natural in maps between the given coefficient modules. -/
lemma coefficientEquiv_naturality (k : I) (g : M →ₗ[R] M') :
    g.comp (coefficientEquiv R I M k).toLinearMap =
      (coefficientEquiv R I M' k).toLinearMap.comp
        (coordinateMap R I k (LinearMap.matrixModuleMap I g)) := by
  apply LinearMap.ext
  intro x
  simp

/-- Reconstruction on a column module is the column map of coefficient recovery. -/
lemma coordinateReconstruction_columns (k : I) :
    (coordinateReconstruction R I (I → M) k).toLinearMap =
      LinearMap.matrixModuleMap I (coefficientEquiv R I M k).toLinearMap := by
  apply LinearMap.ext
  intro v
  ext j
  simp only [LinearEquiv.coe_coe, coordinateReconstruction_apply, Finset.sum_apply,
    single_smul_semiring, one_smul, LinearMap.matrixModuleMap_apply, coefficientEquiv_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- The column triangle identity, without subtraction or cancellation. -/
lemma coordinateReconstruction_triangle (k : I) :
    (coordinateReconstruction R I (I → M) k).toLinearMap.comp
        (LinearMap.matrixModuleMap I (coefficientEquiv R I M k).symm.toLinearMap) =
      LinearMap.id := by
  rw [coordinateReconstruction_columns]
  apply LinearMap.ext
  intro v
  ext i
  exact (coefficientEquiv R I M k).apply_symm_apply (v i)

end Columns

section Index

variable {R : Type uR} {I : Type uI}
  [Semiring R] [Fintype I] [DecidableEq I]
  {N : Type uN} {N' : Type uN'}
  [AddCommMonoid N] [AddCommMonoid N']
  [Module (Matrix I I R) N] [Module (Matrix I I R) N']

variable (R I N)

/-- Change the coordinate summand from `k` to `l` by the matrix unit with row `l`, column `k`.
Its inverse is the matrix unit with row `k`, column `l`. -/
def coordinateChange (k l : I) :
    coordinateSubmodule R I N k ≃ₗ[R] coordinateSubmodule R I N l := by
  letI : Module R N := Module.compHom N (scalar (α := R) I)
  exact
    { __ := (matrixUnitLinearMap R I N l k).restrict fun x _ =>
        (mem_coordinateSubmodule R I N l _).2 (by
          simp only [matrixUnitLinearMap_apply, ← mul_smul, single_mul_single_same, mul_one])
      invFun x := ⟨single k l (1 : R) • (x : N),
        (mem_coordinateSubmodule R I N k _).2 (by simp [← mul_smul])⟩
      left_inv x := Subtype.ext <| by
        change single k l (1 : R) • (single l k (1 : R) • (x : N)) = (x : N)
        simpa [← mul_smul] using (mem_coordinateSubmodule R I N k (x : N)).1 x.2
      right_inv x := Subtype.ext <| by
        change single l k (1 : R) • (single k l (1 : R) • (x : N)) = (x : N)
        simpa [← mul_smul] using (mem_coordinateSubmodule R I N l (x : N)).1 x.2 }

/-- Coordinate change acts on representatives by the corresponding matrix unit. -/
@[simp]
lemma coe_coordinateChange_apply (k l : I) (x : coordinateSubmodule R I N k) :
    (coordinateChange R I N k l x : N) = single l k (1 : R) • (x : N) := rfl

/-- The inverse change of coordinate acts by the opposite matrix unit. -/
lemma coe_coordinateChange_symm_apply (k l : I) (x : coordinateSubmodule R I N l) :
    ((coordinateChange R I N k l).symm x : N) = single k l (1 : R) • (x : N) := rfl

/-- Changing a coordinate to itself is the identity. -/
@[simp]
lemma coordinateChange_refl (k : I) :
    coordinateChange R I N k k = LinearEquiv.refl R (coordinateSubmodule R I N k) := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  exact (mem_coordinateSubmodule R I N k (x : N)).1 x.2

/-- Reversing a coordinate change gives its inverse. -/
@[simp]
lemma coordinateChange_symm (k l : I) :
    (coordinateChange R I N k l).symm = coordinateChange R I N l k := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  rfl

/-- Successive changes of coordinate compose without further choices. -/
@[simp]
lemma coordinateChange_trans (k l m : I) :
    (coordinateChange R I N k l).trans (coordinateChange R I N l m) =
      coordinateChange R I N k m := by
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  simp [← mul_smul]

variable {N}

/-- Changes of coordinate are natural in matrix-linear maps. -/
lemma coordinateChange_naturality (k l : I) (f : N →ₗ[Matrix I I R] N') :
    (coordinateChange R I N' k l).toLinearMap.comp (coordinateMap R I k f) =
      (coordinateMap R I l f).comp (coordinateChange R I N k l).toLinearMap := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  exact (f.map_smul (single l k (1 : R)) (x : N)).symm

/-- Reconstruction is independent of the coordinate after columnwise coordinate change. -/
lemma coordinateReconstruction_coordinateChange (k l : I) :
    (coordinateReconstruction R I N l).toLinearMap.comp
        (LinearMap.matrixModuleMap I (coordinateChange R I N k l).toLinearMap) =
      (coordinateReconstruction R I N k).toLinearMap := by
  apply LinearMap.ext
  intro v
  simp [coordinateReconstruction_apply, ← mul_smul]

/-- Inverse reconstruction is compatible with columnwise coordinate change. -/
lemma coordinateChange_coordinateReconstruction_symm (k l : I) :
    (LinearMap.matrixModuleMap I (coordinateChange R I N k l).toLinearMap).comp
        (coordinateReconstruction R I N k).symm.toLinearMap =
      (coordinateReconstruction R I N l).symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  funext i
  apply Subtype.ext
  simp [← mul_smul]

end Index

section ColumnIndex

variable {R : Type uR} {I : Type uI} {M : Type uM}
  [Semiring R] [Fintype I] [DecidableEq I] [AddCommMonoid M] [Module R M]

variable (R I M)

/-- Coefficient recovery commutes with change of the chosen column coordinate. -/
lemma coefficientEquiv_coordinateChange (k l : I) :
    (coefficientEquiv R I M l).toLinearMap.comp
        (coordinateChange R I (I → M) k l).toLinearMap =
      (coefficientEquiv R I M k).toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, coefficientEquiv_apply,
    coe_coordinateChange_apply, single_smul_semiring, one_smul, Pi.single_eq_same]

end ColumnIndex

section Ring

variable {R : Type uR} {I : Type uI}
  [Ring R] [Fintype I] [DecidableEq I]
  {N : Type uN} {N' : Type uN'} [AddCommGroup N] [AddCommGroup N']
  [Module (Matrix I I R) N] [Module (Matrix I I R) N'] [Module R N] [Module R N']

local notation "RowsR" => @Pi.module I (fun _ : I => R) R _
  (fun _ => inferInstance) (fun _ => @Semiring.toModule R inferInstance)
local notation "MatricesR" => @Pi.module I (fun _ : I => I → R) R _
  (fun _ => inferInstance) (fun _ => RowsR)

variable (R I)

/-- With the ring scalar-tower hypotheses, coordinate restriction agrees on representatives
with Mathlib's restriction, through the identity scalar and range comparisons. -/
lemma coordinateMap_apply_eq_fromMatrixLinear
    (hT : letI : Module R (Matrix I I R) := MatricesR
      IsScalarTower R (Matrix I I R) N)
    (hT' : letI : Module R (Matrix I I R) := MatricesR
      IsScalarTower R (Matrix I I R) N')
    (k : I) (f : N →ₗ[Matrix I I R] N') (x : coordinateSubmodule R I N k) :
    letI : Module R (Matrix I I R) := MatricesR
    letI : IsScalarTower R (Matrix I I R) N := hT
    letI : IsScalarTower R (Matrix I I R) N' := hT'
    (coordinateSubmoduleEquivOfScalar R I N'
      (smul_eq_scalar_smul_of_tower R I N' hT') k (coordinateMap R I k f x) : N') =
      (MatrixModCat.fromMatrixLinear k f
        (coordinateSubmoduleEquivOfScalar R I N
          (smul_eq_scalar_smul_of_tower R I N hT) k x) : N') := by
  let : Module R (Matrix I I R) := MatricesR
  let : IsScalarTower R (Matrix I I R) N := hT
  let : IsScalarTower R (Matrix I I R) N' := hT'
  rfl

end Ring

end Matrix.Module
