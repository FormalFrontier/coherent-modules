/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.Matrix.Module

/-!
# Column actions with matrix-valued coefficients

Matrix-valued columns distinguish the matrix action from pointwise multiplication.
Nested coefficient matrices also distinguish entrywise coefficient actions from either
of the two column actions. The tests include the corresponding weak action classes.
-/

/- Outside the scope the pointwise action remains available. -/
example :
    (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℕ) •
      (Pi.single 1 (Matrix.single 0 0 1) : Fin 2 → Matrix (Fin 2) (Fin 2) ℕ) = 0 := by
  decide

open scoped Matrix.Module

/- All nine selected class values have the same canonical source data. -/
example :
    (inferInstance : Module (Matrix (Fin 2) (Fin 2) ℕ)
      (Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)) =
      Matrix.Module.matrixModuleSemiring (Fin 2) ℕ (Matrix (Fin 2) (Fin 2) ℕ) ∧
    (inferInstance : DistribMulAction (Matrix (Fin 2) (Fin 2) ℕ)
      (Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)) =
      Matrix.Module.matrixDistribMulActionSemiring (Fin 2) ℕ (Matrix (Fin 2) (Fin 2) ℕ) ∧
    (inferInstance : MulAction (Matrix (Fin 2) (Fin 2) ℕ)
      (Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)) =
      Matrix.Module.matrixMulActionSemiring (Fin 2) ℕ (Matrix (Fin 2) (Fin 2) ℕ) ∧
    (inferInstance : SemigroupAction (Matrix (Fin 2) (Fin 2) ℕ)
      (Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)) =
      Matrix.Module.matrixSemigroupActionSemiring (Fin 2) ℕ (Matrix (Fin 2) (Fin 2) ℕ) ∧
    (inferInstance : SMul (Matrix (Fin 2) (Fin 2) ℕ)
      (Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)) =
      Matrix.Module.matrixSMulSemiring (Fin 2) ℕ (Matrix (Fin 2) (Fin 2) ℕ) ∧
    (inferInstance : DistribSMul (Matrix (Fin 2) (Fin 2) ℕ)
      (Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)) =
      Matrix.Module.matrixDistribSMulSemiring (Fin 2) ℕ (Matrix (Fin 2) (Fin 2) ℕ) ∧
    (inferInstance : SMulZeroClass (Matrix (Fin 2) (Fin 2) ℕ)
      (Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)) =
      Matrix.Module.matrixSMulZeroClassSemiring (Fin 2) ℕ (Matrix (Fin 2) (Fin 2) ℕ) ∧
    (inferInstance : MulActionWithZero (Matrix (Fin 2) (Fin 2) ℕ)
      (Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)) =
      Matrix.Module.matrixMulActionWithZeroSemiring (Fin 2) ℕ (Matrix (Fin 2) (Fin 2) ℕ) ∧
    (inferInstance : SMulWithZero (Matrix (Fin 2) (Fin 2) ℕ)
      (Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)) =
      Matrix.Module.matrixSMulWithZeroSemiring (Fin 2) ℕ (Matrix (Fin 2) (Fin 2) ℕ) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/- The matrix-shaped carrier also selects the column data over the regular-self instance. -/
example :
    (inferInstance : Module (Matrix (Fin 2) (Fin 2) ℕ) (Matrix (Fin 2) (Fin 2) ℕ)) =
      Matrix.Module.matrixModuleSemiring (Fin 2) ℕ (Fin 2 → ℕ) := rfl

/- In particular `smul_add` consumes the column action, not the pointwise action. -/
example :
    (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℕ) •
      ((Pi.single 1 (Matrix.single 0 0 1) : Fin 2 → Matrix (Fin 2) (Fin 2) ℕ) + 0) =
      (Pi.single 0 (Matrix.single 0 0 1) : Fin 2 → Matrix (Fin 2) (Fin 2) ℕ) := by
  let A : Matrix (Fin 2) (Fin 2) ℕ := Matrix.single 0 1 1
  let x : Fin 2 → Matrix (Fin 2) (Fin 2) ℕ := Pi.single 1 (Matrix.single 0 0 1)
  have h := smul_add A x 0
  calc
    _ = A • x + A • 0 := h
    _ = _ := by simp [A, x]

example :
    (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℕ) •
      (Pi.single 1 (Matrix.single 0 0 1) : Fin 2 → Matrix (Fin 2) (Fin 2) ℕ) ≠ 0 := by
  intro h
  have h' := congr_fun (congr_fun (congr_fun h 0) 0) 0
  simp at h'

/- Ring overlap uses the new action and agrees with the old Module data. -/
example :
    (Matrix.single 0 1 1 : Matrix (Fin 2) (Fin 2) ℤ) •
      ((Pi.single 1 (Matrix.single 0 0 1) : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ) + 0) =
      (Pi.single 0 (Matrix.single 0 0 1) : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ) := by
  let A : Matrix (Fin 2) (Fin 2) ℤ := Matrix.single 0 1 1
  let x : Fin 2 → Matrix (Fin 2) (Fin 2) ℤ := Pi.single 1 (Matrix.single 0 0 1)
  have h := smul_add A x 0
  calc
    _ = A • x + A • 0 := h
    _ = _ := by simp [A, x]

example :
    Matrix.Module.matrixModuleSemiring (Fin 2) ℤ (Matrix (Fin 2) (Fin 2) ℤ) =
      Matrix.Module.matrixModule (ι := Fin 2) (R := ℤ) (M := Matrix (Fin 2) (Fin 2) ℤ) :=
  Matrix.Module.matrixModuleSemiring_eq_matrixModule

/- The diagonal bridge preserves an explicitly given regular coefficient module,
although the ambient lower-level column action on these coefficients differs. -/
example :
    @SMul.smul (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℕ))
      (Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)
      (Matrix.Module.matrixModuleSemiring (Fin 2) (Matrix (Fin 2) (Fin 2) ℕ)
        (Matrix (Fin 2) (Fin 2) ℕ)
        (hM := @Semiring.toModule _ _)).toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      (Matrix.diagonal (fun _ => Matrix.single 0 1 1))
      (Pi.single 1 (Matrix.single 0 0 1)) = 0 := by
  exact (Matrix.Module.diagonal_const_smul_semiring
    (I := Fin 2) (R := Matrix (Fin 2) (Fin 2) ℕ) (M := Matrix (Fin 2) (Fin 2) ℕ)
    (hM := @Semiring.toModule _ _)
    (Matrix.single 0 1 1) (Pi.single 1 (Matrix.single 0 0 1))).trans (by decide)

/- Both Pi layers of the entrywise coefficient action are pinned to the regular module. -/
example :
    @SMul.smul (Matrix (Fin 2) (Fin 2) ℕ)
      (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℕ))
      (@Pi.module (Fin 2) (fun _ => Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)
        (Matrix (Fin 2) (Fin 2) ℕ) _ (fun _ => Pi.addCommMonoid)
        (fun _ => @Pi.module (Fin 2) (fun _ => Matrix (Fin 2) (Fin 2) ℕ)
          (Matrix (Fin 2) (Fin 2) ℕ) _ (fun _ => inferInstance)
          (fun _ =>
            @Semiring.toModule _ _))).toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      (Matrix.single 0 1 1) (Matrix.single 1 1 (Matrix.single 0 0 1)) = 0 := by
  decide

/- The scalar tower uses these entrywise data, not either nested column action. -/
example :
    @SMul.smul (Matrix (Fin 2) (Fin 2) ℕ) (Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)
      (@Pi.module (Fin 2) (fun _ => Matrix (Fin 2) (Fin 2) ℕ)
        (Matrix (Fin 2) (Fin 2) ℕ) _ (fun _ => inferInstance)
        (fun _ =>
          @Semiring.toModule _ _)).toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      (Matrix.single 0 1 1)
      (@SMul.smul (Matrix (Fin 2) (Fin 2) (Matrix (Fin 2) (Fin 2) ℕ))
        (Fin 2 → Matrix (Fin 2) (Fin 2) ℕ)
        (Matrix.Module.matrixModuleSemiring (Fin 2) (Matrix (Fin 2) (Fin 2) ℕ)
          (Matrix (Fin 2) (Fin 2) ℕ)
          (hM := @Semiring.toModule _ _)).toDistribMulAction.toMulAction.toSemigroupAction.toSMul
        (Matrix.single 1 1 (Matrix.single 0 0 1)) (Pi.single 1 (Matrix.single 0 0 1))) = 0 := by
  have tower := Matrix.Module.matrixModuleSemiring_isScalarTower
    (I := Fin 2) (R := Matrix (Fin 2) (Fin 2) ℕ) (M := Matrix (Fin 2) (Fin 2) ℕ)
    (hM := @Semiring.toModule _ _) (T := Matrix (Fin 2) (Fin 2) ℕ)
    (hTM := @Semiring.toModule _ _)
    (htR := (@Semiring.toModule _ _).toDistribMulAction.toMulAction.toSemigroupAction.toSMul)
    (tau := ⟨fun a b c => mul_assoc a b c⟩)
  exact (@IsScalarTower.smul_assoc _ _ _ _ _ _ tower
    (Matrix.single 0 1 1) (Matrix.single 1 1 (Matrix.single 0 0 1))
    (Pi.single 1 (Matrix.single 0 0 1))).symm.trans (by decide)

/- Empty columns require neither a chosen coordinate nor a nontrivial coefficient module. -/
example {R : Type*} {M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (A : Matrix Empty Empty R) (x : Empty → M) : A • x = 0 := by
  ext i
  exact Empty.elim i
