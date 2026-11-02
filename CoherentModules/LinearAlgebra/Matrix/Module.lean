/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Matrix.Module
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Matrix actions on columns over a semiring

For a semiring `R` and an `R`-semimodule `M`, square matrices act on `I → M` by
`(A • x) i = ∑ j, A i j • x j`. The instances are scoped to `Matrix.Module`.
The coefficient action on `M` is the given one, including when `R` or `M` is itself a
matrix type. Pointwise coefficient actions in the scalar bridges are specified explicitly.

`LinearMap.matrixModuleMap` sends a coefficient-linear map to the corresponding
matrix-linear map on columns, and is additive in that map.

The construction uses the action on natural-linear endomorphisms and
`endVecRingEquivMatrixEnd`. The Ring specialization agrees with the construction in
Mathlib's `LinearAlgebra.Matrix.Module` by Yunzhou Xie.
-/

@[expose] public section

universe uR uI uM uN uP uT

namespace Matrix.Module

variable (I : Type uI) (R : Type uR) (M : Type uM)
  [r : Semiring R] [Fintype I] [DecidableEq I] [aM : AddCommMonoid M] [hM : Module R M]

/-- The matrix action on columns, obtained from the coefficient action on endomorphisms. -/
scoped instance (priority := 1200) matrixModuleSemiring : Module (Matrix I I R) (I → M) := by
  letI : Module ℕ M := AddCommMonoid.toNatModule
  letI : Module ℕ (I → M) :=
    @Pi.module I (fun _ : I => M) ℕ _ (fun _ => aM)
      (fun _ => AddCommMonoid.toNatModule)
  let ρ : R →+* Module.End ℕ M := by
    letI : Module R M := hM
    exact Module.toModuleEnd (R := ℕ) (S := R) (M := M)
  let φ : Matrix I I R →+* Module.End ℕ (I → M) :=
    (endVecRingEquivMatrixEnd I ℕ M).symm.toRingHom.comp ρ.mapMatrix
  letI : Module (Module.End ℕ (I → M)) (I → M) := Module.End.applyModule
  exact Module.compHom (I → M) φ

/-- The distributive multiplicative action underlying the matrix module. -/
scoped instance (priority := 1200) matrixDistribMulActionSemiring :
    DistribMulAction (Matrix I I R) (I → M) :=
  (matrixModuleSemiring I R M).toDistribMulAction

/-- The multiplicative action underlying the matrix module. -/
scoped instance (priority := 1200) matrixMulActionSemiring :
    MulAction (Matrix I I R) (I → M) :=
  (matrixModuleSemiring I R M).toDistribMulAction.toMulAction

/-- The semigroup action underlying the matrix module. -/
scoped instance (priority := 1200) matrixSemigroupActionSemiring :
    SemigroupAction (Matrix I I R) (I → M) :=
  (matrixModuleSemiring I R M).toDistribMulAction.toMulAction.toSemigroupAction

/-- Scalar multiplication underlying the matrix module. -/
scoped instance (priority := 1200) matrixSMulSemiring : SMul (Matrix I I R) (I → M) :=
  (matrixModuleSemiring I R M).toDistribMulAction.toMulAction.toSemigroupAction.toSMul

/-- Distributive scalar multiplication underlying the matrix module. -/
scoped instance (priority := 1200) matrixDistribSMulSemiring :
    DistribSMul (Matrix I I R) (I → M) :=
  @DistribMulAction.toDistribSMul _ _ _ _
    (matrixModuleSemiring I R M).toDistribMulAction

/-- The zero-preserving scalar action underlying the matrix module. -/
scoped instance (priority := 1200) matrixSMulZeroClassSemiring :
    SMulZeroClass (Matrix I I R) (I → M) :=
  (matrixDistribSMulSemiring I R M).toSMulZeroClass

/-- The multiplicative action with zero underlying the matrix module. -/
scoped instance (priority := 1200) matrixMulActionWithZeroSemiring :
    MulActionWithZero (Matrix I I R) (I → M) :=
  @Module.toMulActionWithZero _ _ _ _ (matrixModuleSemiring I R M)

/-- Scalar multiplication with zero underlying the matrix module. -/
scoped instance (priority := 1200) matrixSMulWithZeroSemiring :
    SMulWithZero (Matrix I I R) (I → M) :=
  @MulActionWithZero.toSMulWithZero _ _ _ _
    (matrixMulActionWithZeroSemiring I R M)

variable {I R M}

/-- Matrix multiplication on a column is the finite sum of coefficient actions. -/
lemma smul_def_semiring (A : Matrix I I R) (x : I → M) :
    A • x = fun i ↦ ∑ j : I, A i j • x j := rfl

/-- Matrix multiplication on a column as a sum of columns. -/
lemma smul_def'_semiring (A : Matrix I I R) (x : I → M) :
    A • x = ∑ j : I, fun i ↦ A i j • x j := by
  ext i
  simp [smul_def_semiring]

/-- The coordinate formula for matrix multiplication on columns. -/
@[simp]
lemma smul_apply_semiring (A : Matrix I I R) (x : I → M) (i : I) :
    (A • x) i = ∑ j : I, A i j • x j := rfl

/-- A matrix unit selects one coordinate and places its scalar multiple in another. -/
@[simp]
lemma single_smul_semiring (i j : I) (r₀ : R) (x : I → M) :
    Matrix.single i j r₀ • x = Pi.single i (r₀ • x j) := by
  ext i'
  rw [smul_apply_semiring, Fintype.sum_eq_single j]
  · obtain rfl | hi := eq_or_ne i i' <;> simp [*]
  · intro j' hj
    simp [hj.symm]

/-- A constant diagonal acts by the pointwise action of the given coefficient module. -/
lemma diagonal_const_smul_semiring (r₀ : R) (x : I → M) :
    diagonal (fun _ : I ↦ r₀) • x =
      @SMul.smul R (I → M)
        (@Pi.module I (fun _ : I => M) R r
          (fun _ => aM) (fun _ => hM)).toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        r₀ x := by
  ext i
  change (diagonal (fun _ : I ↦ r₀) • x) i = r₀ • x i
  simp [Matrix.diagonal_apply]

/-- A scalar matrix acts by the pointwise action of the given coefficient module. -/
lemma scalar_smul_semiring (r₀ : R) (x : I → M) :
    Matrix.scalar I r₀ • x =
      @SMul.smul R (I → M)
        (@Pi.module I (fun _ : I => M) R r
          (fun _ => aM) (fun _ => hM)).toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        r₀ x := by
  exact diagonal_const_smul_semiring r₀ x

/-- An external scalar tower extends to entrywise scalars on matrices and columns. -/
theorem matrixModuleSemiring_isScalarTower
    {T : Type uT} [t : Semiring T] [hTM : Module T M] [htR : SMul T R]
    [tau : @IsScalarTower T R M htR
      hM.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      hTM.toDistribMulAction.toMulAction.toSemigroupAction.toSMul] :
    @IsScalarTower T (Matrix I I R) (I → M)
      (@Pi.instSMul _ _ _ (fun _ : I =>
        (@Pi.instSMul _ _ _ (fun _ : I => htR) : SMul T (I → R))))
      (matrixModuleSemiring I R M).toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      (@Pi.module I (fun _ : I => M) T t
        (fun _ => aM) (fun _ => hTM)).toDistribMulAction.toMulAction.toSemigroupAction.toSMul where
  smul_assoc s A x := by
    ext i
    change (∑ j : I, (s • A i j) • x j) = s • ∑ j : I, A i j • x j
    simp only [Finset.smul_sum, smul_assoc]

section Ring

variable {R : Type uR} {M : Type uM} [Ring R] [AddCommGroup M] [hM : Module R M]

/-- Over a ring the semiring construction equals Mathlib's matrix module data. -/
theorem matrixModuleSemiring_eq_matrixModule :
    matrixModuleSemiring I R M = @matrixModule I R M _ _ _ _ hM := by
  apply Module.ext'
  intro A x
  rfl

end Ring

end Matrix.Module

namespace LinearMap

open scoped Matrix.Module

variable {R : Type uR} {M : Type uM} {N : Type uN} {P : Type uP}
  [r : Semiring R] [aM : AddCommMonoid M] [hM : Module R M]
  [aN : AddCommMonoid N] [hN : Module R N] [AddCommMonoid P] [Module R P]
  (I : Type uI) [Fintype I] [DecidableEq I]

/-- Applying a coefficient-linear map at every coordinate gives a matrix-linear map.
This construction is additive in the coefficient-linear map. -/
def matrixModuleMap : (M →ₗ[R] N) →+ ((I → M) →ₗ[Matrix I I R] (I → N)) where
  toFun f :=
    { toFun := fun x i ↦ f (x i)
      map_add' := fun x y ↦ by ext i; exact f.map_add (x i) (y i)
      map_smul' := fun A x ↦ by ext i; simp }
  map_zero' := by ext x i; rfl
  map_add' f g := by ext x i; rfl

/-- The induced map applies the coefficient-linear map coordinatewise. -/
@[simp]
lemma matrixModuleMap_apply (f : M →ₗ[R] N) (x : I → M) (i : I) :
    matrixModuleMap I f x i = f (x i) := rfl

/-- The identity coefficient map induces the identity map on columns. -/
@[simp]
lemma matrixModuleMap_id :
    matrixModuleMap I (LinearMap.id : M →ₗ[R] M) =
      (LinearMap.id : (I → M) →ₗ[Matrix I I R] (I → M)) := by
  ext x i
  rfl

/-- Inducing maps on columns preserves composition. -/
lemma matrixModuleMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    matrixModuleMap I (g.comp f) = (matrixModuleMap I g).comp (matrixModuleMap I f) := by
  ext x i
  rfl

private theorem transport_apply {S X Y : Type*} [Semiring S]
    [AddCommMonoid X] [AddCommMonoid Y]
    {m₁ m₂ : Module S X} {n₁ n₂ : Module S Y} (hm : m₁ = m₂) (hn : n₁ = n₂)
    (f : @LinearMap S S _ _ (RingHom.id S) X Y _ _ m₁ n₁) (x : X) :
    (Eq.mp (congrArg₂ (fun m n => @LinearMap S S _ _ (RingHom.id S) X Y _ _ m n)
      hm hn) f) x = f x := by
  cases hm
  cases hn
  rfl

section Ring

variable {R : Type uR} {M : Type uM} {N : Type uN}
  [Ring R] [AddCommGroup M] [hM : Module R M] [AddCommGroup N] [hN : Module R N]

/-- After transport along the equality of module data, the induced map agrees with
Mathlib's map on matrix modules over a ring. -/
lemma matrixModuleMap_eq_mapMatrixModule (f : M →ₗ[R] N) :
    Eq.mp (congrArg₂
      (fun (m : Module (Matrix I I R) (I → M)) (n : Module (Matrix I I R) (I → N)) =>
        @LinearMap (Matrix I I R) (Matrix I I R) _ _ (RingHom.id _) (I → M) (I → N)
          _ _ m n)
      (Matrix.Module.matrixModuleSemiring_eq_matrixModule (I := I) (R := R) (M := M))
      (Matrix.Module.matrixModuleSemiring_eq_matrixModule (I := I) (R := R) (M := N)))
      (matrixModuleMap I f) = @LinearMap.mapMatrixModule I R M N _ _ _ _ hM _ hN f := by
  apply DFunLike.ext
  intro x
  apply funext
  intro i
  rw [transport_apply
    (Matrix.Module.matrixModuleSemiring_eq_matrixModule (I := I) (R := R) (M := M))
    (Matrix.Module.matrixModuleSemiring_eq_matrixModule (I := I) (R := R) (M := N))]
  rfl

end Ring

end LinearMap
