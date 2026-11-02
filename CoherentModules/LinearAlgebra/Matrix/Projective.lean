/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.Matrix.Module
public import CoherentModules.LinearAlgebra.Projective.RestrictScalars
public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Projective matrix-column semimodules

For a finite type `I`, the canonical matrix module on `I → M` is projective over
`Matrix I I R` exactly when `I` is empty or the given coefficient module `M` is projective
over `R`. In the inhabited case, columns of the regular coefficient module are a retract
of the regular matrix module. Finite-index interchange with finitely supported functions
then carries a coefficient free splitting to a matrix-linear splitting.

The proof uses Mathlib's projectivity, splitting, and finitely supported-function APIs.
Coefficient actions on functions are pointwise actions of the given module; the regular
matrix module in the retract is the one furnished by `Semiring.toModule`.
-/

@[expose] public section

universe uR uI uM uΓ

namespace Matrix.Module

variable {R : Type uR} {I : Type uI} {M : Type uM}
  [r : Semiring R] [Fintype I] [DecidableEq I]
  [aM : AddCommMonoid M] [hM : Module R M]

private theorem projective_regular_columns (k : I) :
    @Module.Projective (Matrix I I R) _ (I → R) _
      (@matrixModuleSemiring I R R r _ _ _ (@Semiring.toModule R r)) := by
  classical
  let S := Matrix I I R
  let _ : Module S (I → R) :=
    @matrixModuleSemiring I R R r _ _ _ (@Semiring.toModule R r)
  let e : I → R := Pi.single k 1
  let π : @LinearMap S S _ _ (RingHom.id S) S (I → R) _ _
      (@Semiring.toModule S _)
      (@matrixModuleSemiring I R R r _ _ _ (@Semiring.toModule R r)) :=
    LinearMap.toSpanSingleton S (I → R) e
  have hπ (A : S) : π A = A.col k := by
    change A • (Pi.single k (1 : R) : I → R) = A.col k
    rw [smul_def_semiring]
    exact Matrix.mulVec_single_one A k
  let σ : @LinearMap S S _ _ (RingHom.id S) (I → R) S _ _
      (@matrixModuleSemiring I R R r _ _ _ (@Semiring.toModule R r))
      (@Semiring.toModule S _) :=
    { toFun := fun v => Matrix.vecMulVec v e
      map_add' := fun v w => by
        ext i j
        change (v i + w i) * e j = v i * e j + w i * e j
        exact add_mul _ _ _
      map_smul' := fun A v => by
        change Matrix.vecMulVec (A • v) e = A * Matrix.vecMulVec v e
        rw [smul_def_semiring]
        exact (Matrix.mul_vecMulVec A v e).symm }
  have hsplit : π.comp σ = LinearMap.id := by
    ext v i
    change π (σ v) i = v i
    rw [hπ]
    change v i * (Pi.single k (1 : R) : I → R) k = v i
    simp
  let _ : @Module.Projective S _ S _ (@Semiring.toModule S _) :=
    Module.Projective.of_free
  exact Module.Projective.of_split σ π hsplit

private theorem projective_finsupp_columns (Γ : Type uΓ) (k : I) :
    @Module.Projective (Matrix I I R) _ (I → Γ →₀ R) _
      (@matrixModuleSemiring I R (Γ →₀ R) r _ _ _
        (@Finsupp.module (α := Γ) (M := R) (R := R) r _ (@Semiring.toModule R r))) := by
  classical
  let S := Matrix I I R
  let _ : Module S (I → R) :=
    @matrixModuleSemiring I R R r _ _ _ (@Semiring.toModule R r)
  let _ : Module S (I → Γ →₀ R) :=
    @matrixModuleSemiring I R (Γ →₀ R) r _ _ _
      (@Finsupp.module (α := Γ) (M := R) (R := R) r _ (@Semiring.toModule R r))
  let e : (I → Γ →₀ R) ≃ₗ[ℕ] Γ →₀ (I → R) :=
    (Finsupp.linearEquivFunOnFinite ℕ (Γ →₀ R) I).symm ≪≫ₗ
      (Finsupp.curryLinearEquiv ℕ).symm ≪≫ₗ
      Finsupp.lcongr (Equiv.prodComm I Γ) (LinearEquiv.refl ℕ R) ≪≫ₗ
      Finsupp.curryLinearEquiv ℕ ≪≫ₗ
      Finsupp.mapRange.linearEquiv (Finsupp.linearEquivFunOnFinite ℕ R I)
  have he (x : I → Γ →₀ R) (γ : Γ) (i : I) : e x γ i = x i γ := by
    simp [e, Finsupp.lcongr_apply_apply, Finsupp.curryLinearEquiv]
  let eS : (I → Γ →₀ R) ≃ₗ[S] Γ →₀ (I → R) :=
    { e.toAddEquiv with
      map_smul' := fun A x => by
        ext γ i
        change e (A • x) γ i = (A • e x γ) i
        rw [he]
        calc
          ((A • x) i) γ = (∑ j : I, A i j • x j) γ :=
            congrArg (fun f : Γ →₀ R => f γ)
              (smul_apply_semiring (I := I) (R := R) (M := Γ →₀ R)
                (hM := @Finsupp.module (α := Γ) (M := R) (R := R) r _
                  (@Semiring.toModule R r)) A x i)
          _ = ∑ j : I, A i j • e x γ j := by
            simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, he]
          _ = (A • e x γ) i :=
            (smul_apply_semiring (I := I) (R := R) (M := R)
              (hM := @Semiring.toModule R r) A (e x γ) i).symm }
  let _ : Module.Projective S (I → R) := projective_regular_columns k
  let _ : Module.Projective S (Γ →₀ (I → R)) :=
    Module.Projective.of_equiv'
      (finsuppLequivDFinsupp (ι := Γ) (M := I → R) S).symm
  exact Module.Projective.of_equiv' eS.symm

private theorem projective_columns_of_projective (k : I)
    (h : @Module.Projective R r M aM hM) :
    @Module.Projective (Matrix I I R) _ (I → M) _
      (@matrixModuleSemiring I R M r _ _ aM hM) := by
  classical
  let S := Matrix I I R
  let _ : Module S (I → M) := @matrixModuleSemiring I R M r _ _ aM hM
  let _ : Module S (I → M →₀ R) :=
    @matrixModuleSemiring I R (M →₀ R) r _ _ _
      (@Finsupp.module (α := M) (M := R) (R := R) r _ (@Semiring.toModule R r))
  let _ : Module.Projective S (I → M →₀ R) := projective_finsupp_columns M k
  obtain ⟨s, hs⟩ := Module.projective_def'.mp h
  refine Module.Projective.of_split (LinearMap.matrixModuleMap I s)
    (LinearMap.matrixModuleMap I (Finsupp.linearCombination R id)) ?_
  rw [← LinearMap.matrixModuleMap_comp, hs, LinearMap.matrixModuleMap_id]

private theorem projective_of_projective_columns (k : I)
    (h : @Module.Projective (Matrix I I R) _ (I → M) _
      (@matrixModuleSemiring I R M r _ _ aM hM)) :
    @Module.Projective R r M aM hM := by
  let S := Matrix I I R
  let hPRR : Module R (I → R) :=
    @Pi.module I (fun _ : I => R) R r (fun _ => inferInstance)
      (fun _ => @Semiring.toModule R r)
  let hBR : Module R S :=
    @Pi.module I (fun _ : I => I → R) R r (fun _ => inferInstance) (fun _ => hPRR)
  let hPM : Module R (I → M) :=
    @Pi.module I (fun _ : I => M) R r (fun _ => aM) (fun _ => hM)
  let _ : Module R S := hBR
  let _ : Module R (I → M) := hPM
  let _ : Module S (I → M) := @matrixModuleSemiring I R M r _ _ aM hM
  let _ : Module.Projective S (I → M) := h
  let hRS : @Module.Projective R r S _ hBR :=
    Module.Projective.of_basis (Pi.basis fun _ : I => Pi.basisFun R I)
  let hRSS : @IsScalarTower R S S
      (hBR.toDistribMulAction.toMulAction.toSemigroupAction.toSMul)
      ((@Semiring.toModule S _).toDistribMulAction.toMulAction.toSemigroupAction.toSMul)
      (hBR.toDistribMulAction.toMulAction.toSemigroupAction.toSMul) :=
    Matrix.Semiring.isScalarTower
  let hRSM : @IsScalarTower R S (I → M)
      (hBR.toDistribMulAction.toMulAction.toSemigroupAction.toSMul)
      ((@matrixModuleSemiring I R M r _ _
        aM hM).toDistribMulAction.toMulAction.toSemigroupAction.toSMul)
      (hPM.toDistribMulAction.toMulAction.toSemigroupAction.toSMul) :=
    matrixModuleSemiring_isScalarTower (I := I) (R := R) (M := M) (T := R)
      (hM := hM) (hTM := hM)
      (htR := (@Semiring.toModule R r).toDistribMulAction.toMulAction.toSemigroupAction.toSMul)
  let _ : @Module.Projective R r (I → M) _ hPM :=
    @Module.Projective.restrictScalars (R := R) (S := S) (M := I → M) r _ _ hBR hPM
      (@matrixModuleSemiring I R M r _ _ aM hM) hRSS hRSM hRS h
  let ι : @LinearMap R R r r (RingHom.id R) M (I → M) aM _ hM hPM :=
    LinearMap.single R (fun _ : I => M) k
  let p : @LinearMap R R r r (RingHom.id R) (I → M) M _ aM hPM hM :=
    LinearMap.proj k
  exact Module.Projective.of_split ι p
    (LinearMap.proj_comp_single_same R (fun _ : I => M) k)

/-- The canonical module of columns is projective over the matrix semiring exactly when
its index type is empty or its given coefficient module is projective. -/
theorem projective_iff :
    @Module.Projective (Matrix I I R) _ (I → M) _
      (@matrixModuleSemiring I R M r _ _ aM hM) ↔
      IsEmpty I ∨ @Module.Projective R r M aM hM := by
  classical
  by_cases hI : Nonempty I
  · let k : I := Classical.choice hI
    refine ⟨fun h => Or.inr (projective_of_projective_columns k h), ?_⟩
    rintro (h | h)
    · exact (h.false k).elim
    · exact projective_columns_of_projective k h
  · have hE : IsEmpty I := ⟨fun i => hI ⟨i⟩⟩
    let _ : IsEmpty I := hE
    have hp : @Module.Projective (Matrix I I R) _ (I → M) _
        (@matrixModuleSemiring I R M r _ _ aM hM) := by
      let _ : Module (Matrix I I R) (I → M) := @matrixModuleSemiring I R M r _ _ aM hM
      infer_instance
    exact ⟨fun _ => Or.inl hE, fun _ => hp⟩

/-- For an inhabited finite index type, canonical columns are projective over the matrix
semiring exactly when the given coefficient module is projective. -/
theorem projective_iff_of_nonempty [Nonempty I] :
    @Module.Projective (Matrix I I R) _ (I → M) _
      (@matrixModuleSemiring I R M r _ _ aM hM) ↔
      @Module.Projective R r M aM hM := by
  classical
  refine ⟨fun h => ?_, fun h => projective_iff.mpr (Or.inr h)⟩
  rcases projective_iff.mp h with h | h
  · exact (h.false (Classical.choice (inferInstance : Nonempty I))).elim
  · exact h

end Matrix.Module
