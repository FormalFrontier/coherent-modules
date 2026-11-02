/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.Matrix.Module
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Order.JordanHolder
public import Mathlib.Order.RelIso.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Submodules of matrix column modules

For a semiring `R`, an `R`-semimodule `M`, and a finite nonempty index type `I`, the
submodules of `M` correspond bijectively to the submodules of `I → M` stable under all square
matrices. The forward map requires every coordinate to belong to the coefficient submodule.
The inverse requires every single-coordinate column to belong to the matrix submodule.

The adjunction and the inverse identity on column submodules hold even when `I` is empty.
For nonempty finite `I`, these maps form `Submodule.matrixColumnsOrderIso`. The inverse is
also the image of any coordinate projection after restriction to the coefficient semiring.
The coefficient action on columns is the given action on `M`; the action on matrices used
for restriction of scalars is the entrywise regular action of `R`.

The correspondence transports Noetherianity, Artinianity, and simplicity of the submodule
lattice over any semiring. The bridges for the stock `IsSimpleModule` and
`IsSemisimpleModule` classes use a ring and an additive commutative group, as required by
those classes.

For a nonempty index type, write `e := Submodule.matrixColumnsOrderIso`. Composition series
transport directly by `s.map ⟨e, fun h => (apply_covBy_apply_iff e).2 h⟩`.
The stock `RelSeries.map_length`, `RelSeries.head_map`, and `RelSeries.last_map` describe
length and endpoints; `e.map_bot` and `e.map_top` preserve full endpoints.
In the ring and additive-group setting, `Module.coe_length` and
`Order.krullDim_eq_of_orderIso e` give equality of the matrix-module length of `I → M`
with the coefficient-module length of `M`, not with the restricted coefficient length of
`I → M`. Empty columns have length zero by the stock subsingleton machinery.
-/

@[expose] public section

universe uR uM uI

open scoped Matrix.Module

namespace Submodule

variable {R : Type uR} {M : Type uM} {I : Type uI}
  [r : Semiring R] [Fintype I] [DecidableEq I] [aM : AddCommMonoid M] [hM : Module R M]

/-- The matrix submodule consisting of columns whose coordinates all belong to `N`. -/
def matrixColumns (N : Submodule R M) : Submodule (Matrix I I R) (I → M) where
  carrier := {x | ∀ i, x i ∈ N}
  zero_mem' := fun _ => N.zero_mem
  add_mem' hx hy i := N.add_mem (hx i) (hy i)
  smul_mem' A x hx i := by
    rw [Matrix.Module.smul_apply_semiring]
    exact N.sum_mem fun j _ => N.smul_mem (A i j) (hx j)

/-- Membership in the matrix submodule associated to a coefficient submodule is coordinatewise. -/
@[simp]
theorem mem_matrixColumns {N : Submodule R M} {x : I → M} :
    x ∈ N.matrixColumns (I := I) ↔ ∀ i, x i ∈ N := Iff.rfl

/-- A single-coordinate column belongs to `matrixColumns N` exactly when its entry belongs to `N`.
-/
theorem single_mem_matrixColumns (N : Submodule R M) (i : I) (m : M) :
    Pi.single i m ∈ N.matrixColumns (I := I) ↔ m ∈ N := by
  constructor
  · intro hm
    simpa only [Pi.single_eq_same] using mem_matrixColumns.mp hm i
  · intro hm
    apply mem_matrixColumns.mpr
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Pi.single_eq_same] using hm
    · simp [hji]

/-- The coefficient submodule whose elements give single-coordinate columns in `P` at every index.
-/
def columnCoefficients (P : Submodule (Matrix I I R) (I → M)) : Submodule R M where
  carrier := {m | ∀ i, Pi.single i m ∈ P}
  zero_mem' i := by simpa only [Pi.single_zero] using P.zero_mem
  add_mem' hx hy i := by
    simpa only [Pi.single_add] using P.add_mem (hx i) (hy i)
  smul_mem' a m hm i := by
    simpa only [Matrix.Module.single_smul_semiring, Pi.single_eq_same] using
      P.smul_mem (Matrix.single i i a) (hm i)

/-- The inverse coefficient submodule requires membership of every single-coordinate column. -/
@[simp]
theorem mem_columnCoefficients {P : Submodule (Matrix I I R) (I → M)} {m : M} :
    m ∈ P.columnCoefficients ↔ ∀ i, Pi.single i m ∈ P := Iff.rfl

/-- Coordinatewise columns and single-coordinate coefficients form an adjoint pair for every
finite index type, including the empty type. -/
theorem matrixColumns_le_iff (N : Submodule R M)
    (P : Submodule (Matrix I I R) (I → M)) :
    N.matrixColumns (I := I) ≤ P ↔ N ≤ P.columnCoefficients := by
  constructor
  · intro h m hm
    apply mem_columnCoefficients.mpr
    intro i
    exact h ((single_mem_matrixColumns N i m).mpr hm)
  · intro h x hx
    rw [← LinearMap.sum_single_apply (fun _ : I => M) x]
    exact P.sum_mem fun i _ =>
      mem_columnCoefficients.mp (h (mem_matrixColumns.mp hx i)) i

/-- Every matrix-stable submodule is recovered from its single-coordinate coefficients. -/
@[simp]
theorem matrixColumns_columnCoefficients (P : Submodule (Matrix I I R) (I → M)) :
    P.columnCoefficients.matrixColumns (I := I) = P := by
  apply le_antisymm
  · exact (matrixColumns_le_iff _ P).mpr le_rfl
  · intro x hx
    apply mem_matrixColumns.mpr
    intro i
    apply mem_columnCoefficients.mpr
    intro j
    simpa only [Matrix.Module.single_smul_semiring, one_smul] using
      P.smul_mem (Matrix.single j i 1) hx

/-- A coefficient submodule is recovered from its columns when the index type is nonempty. -/
@[simp]
theorem columnCoefficients_matrixColumns [Nonempty I] (N : Submodule R M) :
    (N.matrixColumns (I := I)).columnCoefficients = N := by
  ext m
  constructor
  · intro hm
    obtain ⟨i⟩ := ‹Nonempty I›
    exact (single_mem_matrixColumns N i m).mp (mem_columnCoefficients.mp hm i)
  · intro hm
    apply mem_columnCoefficients.mpr
    intro i
    exact (single_mem_matrixColumns N i m).mpr hm

/-- With no coordinates, every element satisfies the single-coordinate membership condition. -/
@[simp]
theorem columnCoefficients_eq_top_of_isEmpty [IsEmpty I]
    (P : Submodule (Matrix I I R) (I → M)) : P.columnCoefficients = ⊤ := by
  apply top_unique
  intro m _
  apply mem_columnCoefficients.mpr
  intro i
  exact isEmptyElim i

/-- The order isomorphism between coefficient submodules and matrix-stable column submodules. -/
def matrixColumnsOrderIso [Nonempty I] :
    Submodule R M ≃o Submodule (Matrix I I R) (I → M) where
  toFun := matrixColumns
  invFun := columnCoefficients
  left_inv := columnCoefficients_matrixColumns
  right_inv := matrixColumns_columnCoefficients
  map_rel_iff' := by
    intro N N'
    change N.matrixColumns (I := I) ≤ N'.matrixColumns (I := I) ↔ N ≤ N'
    rw [matrixColumns_le_iff, columnCoefficients_matrixColumns]

@[simp]
theorem matrixColumnsOrderIso_apply [Nonempty I] (N : Submodule R M) :
    matrixColumnsOrderIso (I := I) N = N.matrixColumns (I := I) := rfl

@[simp]
theorem matrixColumnsOrderIso_symm_apply [Nonempty I]
    (P : Submodule (Matrix I I R) (I → M)) :
    (matrixColumnsOrderIso (I := I)).symm P = P.columnCoefficients := rfl

section CoordinateImage

local notation "hPM" =>
  (@Pi.module I (fun _ : I => M) R r (fun _ => aM) (fun _ => hM))
local notation "hPRR" =>
  (@Pi.module I (fun _ : I => R) R r (fun _ => inferInstance)
    (fun _ => @Semiring.toModule R r))
local notation "hBR" =>
  (@Pi.module I (fun _ : I => I → R) R r (fun _ => inferInstance) (fun _ => hPRR))
local notation "hCM" => (@Matrix.Module.matrixModuleSemiring I R M r _ _ aM hM)
local notation "hRSM" =>
  (Matrix.Module.matrixModuleSemiring_isScalarTower (I := I) (R := R) (M := M) (T := R)
    (hM := hM) (hTM := hM)
    (htR := @SemigroupAction.toSMul R R _ <|
      @MulAction.toSemigroupAction R R _ <|
        @DistribMulAction.toMulAction R R _ _ <|
          @Module.toDistribMulAction R R r _ (@Semiring.toModule R r)))

/-- The inverse coefficient submodule is the image of any `R`-linear coordinate projection,
with the column module restricted using the entrywise regular action on matrices and the
given pointwise coefficient action on columns. No separate nonemptiness assumption is needed.
-/
theorem columnCoefficients_eq_map_proj (P : Submodule (Matrix I I R) (I → M)) (i : I) :
    P.columnCoefficients =
      (@Submodule.restrictScalars R (Matrix I I R) (I → M) _ _ r hPM hCM
        (hBR).toDistribMulAction.toMulAction.toSemigroupAction.toSMul hRSM P).map
        (LinearMap.proj i : @LinearMap R R r r (RingHom.id R) (I → M) M _ aM hPM hM) := by
  let : Module R (I → M) := hPM
  let : Module R (Matrix I I R) := hBR
  let : IsScalarTower R (Matrix I I R) (I → M) := hRSM
  ext m
  constructor
  · intro hm
    exact mem_map.mpr ⟨Pi.single i m, mem_columnCoefficients.mp hm i, by simp⟩
  · intro hm
    obtain ⟨x, hx, hxm⟩ := mem_map.mp hm
    have hxi : x i = m := hxm
    apply mem_columnCoefficients.mpr
    intro j
    simpa only [Matrix.Module.single_smul_semiring, one_smul, hxi] using
      P.smul_mem (Matrix.single j i 1) hx

end CoordinateImage

end Submodule

namespace Matrix.Module

section Semiring

variable {R : Type uR} {M : Type uM} {I : Type uI}
  [r : Semiring R] [aM : AddCommMonoid M] [hM : Module R M]
  [Fintype I] [DecidableEq I]

/-- The matrix module of columns is Noetherian exactly when the index type is empty or the
coefficient module is Noetherian. -/
theorem isNoetherian_iff :
    IsNoetherian (Matrix I I R) (I → M) ↔ IsEmpty I ∨ IsNoetherian R M := by
  cases isEmpty_or_nonempty I with
  | inl h =>
    let := h
    exact iff_of_true (isNoetherian_of_finite (Matrix I I R) (I → M)) (Or.inl h)
  | inr h =>
    let := h
    have hn : ¬ IsEmpty I := by
      intro hi
      let := hi
      exact isEmptyElim (Classical.choice h)
    let e := Submodule.matrixColumnsOrderIso (R := R) (M := M) (I := I)
    rw [_root_.isNoetherian_iff, or_iff_right hn, _root_.isNoetherian_iff]
    exact (e.surjective.wellFounded_iff
      (fun {a b} => (e.lt_iff_lt (x := b) (y := a)).symm)).symm

/-- The matrix module of columns is Artinian exactly when the index type is empty or the
coefficient module is Artinian. -/
theorem isArtinian_iff :
    IsArtinian (Matrix I I R) (I → M) ↔ IsEmpty I ∨ IsArtinian R M := by
  cases isEmpty_or_nonempty I with
  | inl h =>
    let := h
    exact iff_of_true isArtinian_of_finite (Or.inl h)
  | inr h =>
    let := h
    have hn : ¬ IsEmpty I := by
      intro hi
      let := hi
      exact isEmptyElim (Classical.choice h)
    let e := Submodule.matrixColumnsOrderIso (R := R) (M := M) (I := I)
    rw [_root_.isArtinian_iff, or_iff_right hn, _root_.isArtinian_iff]
    exact (e.surjective.wellFounded_iff
      (fun {a b} => (e.lt_iff_lt (x := a) (y := b)).symm)).symm

/-- The column submodule lattice is simple exactly when there is a coordinate and the
coefficient submodule lattice is simple. -/
theorem isSimpleOrder_submodule_iff :
    IsSimpleOrder (Submodule (Matrix I I R) (I → M)) ↔
      Nonempty I ∧ IsSimpleOrder (Submodule R M) := by
  cases isEmpty_or_nonempty I with
  | inl h =>
    let := h
    have hn : ¬ IsSimpleOrder (Submodule (Matrix I I R) (I → M)) := by
      intro hs
      let := hs
      exact bot_ne_top (Subsingleton.elim (⊥ : Submodule (Matrix I I R) (I → M)) ⊤)
    exact iff_of_false hn (fun hc => isEmptyElim (Classical.choice hc.1))
  | inr h =>
    let := h
    rw [and_iff_right h]
    exact (Submodule.matrixColumnsOrderIso (R := R) (M := M) (I := I)).isSimpleOrder_iff.symm

end Semiring

section Ring

variable {R : Type uR} {M : Type uM} {I : Type uI}
  [r : Ring R] [aM : AddCommGroup M] [hM : Module R M]
  [Fintype I] [DecidableEq I]

/-- Over a ring, the matrix module of columns is simple exactly when there is a coordinate
and the coefficient module is simple. -/
theorem isSimpleModule_iff :
    IsSimpleModule (Matrix I I R) (I → M) ↔ Nonempty I ∧ IsSimpleModule R M := by
  rw [_root_.isSimpleModule_iff, _root_.isSimpleModule_iff]
  exact isSimpleOrder_submodule_iff

/-- Over a ring, the matrix module of columns is semisimple exactly when the index type is
empty or the coefficient module is semisimple. -/
theorem isSemisimpleModule_iff :
    IsSemisimpleModule (Matrix I I R) (I → M) ↔
      IsEmpty I ∨ IsSemisimpleModule R M := by
  cases isEmpty_or_nonempty I with
  | inl h =>
    let := h
    have hs : IsSemisimpleModule (Matrix I I R) (I → M) := by
      rw [_root_.isSemisimpleModule_iff]
      exact Subsingleton.instComplementedLattice
    exact iff_of_true hs (Or.inl h)
  | inr h =>
    let := h
    have hn : ¬ IsEmpty I := by
      intro hi
      let := hi
      exact isEmptyElim (Classical.choice h)
    rw [or_iff_right hn, _root_.isSemisimpleModule_iff, _root_.isSemisimpleModule_iff]
    exact (Submodule.matrixColumnsOrderIso (R := R) (M := M) (I := I)).complementedLattice_iff.symm

end Ring

end Matrix.Module
