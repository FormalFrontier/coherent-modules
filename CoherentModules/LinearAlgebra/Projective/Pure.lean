/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Finiteness.Pure
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Finite projectivity under pure scalar extension

Finite projectivity descends along a central scalar extension with injective
canonical tensor units. The scalar algebra may be noncommutative and need not
be flat. Both the module and its scalar extension retain their given actions.

The proof descends finite presentation first, then encodes a splitting of a
finite presentation by finitely many linear equations. Membership reflection
for extended submodules descends a solution of these equations.

## References

The proof uses Mathlib's finite-projective finite-presentation criterion,
projective lifting, finite-product tensor equivalences and quotient maps, and
the tensor-unit membership and finiteness descent APIs.
-/

@[expose] public section

universe uR uS uM

open scoped BigOperators TensorProduct

namespace Module

/-- Finite projectivity descends along a central scalar extension whose tensor
units are injective on modules in the indicated test universe. The scalar
algebra need not be commutative or flat, and the original module need only be
an additive commutative monoid. -/
theorem finite_projective_of_tensorProduct_of_injective
    (R : Type uR) (M : Type uM) [CommRing R]
    [AddCommMonoid M] [Module R M]
    (S : Type uS) [Semiring S] [Algebra R S]
    [Module.Finite S (S ⊗[R] M)]
    [Module.Projective S (S ⊗[R] M)]
    (hunit : ∀ (N : Type (max uR uM)) [AddCommMonoid N] [Module R N],
      Function.Injective (TensorProduct.mk R S N 1)) :
    Module.Finite R M ∧ Module.Projective R M := by
  classical
  let : Module.Finite R M :=
    Module.Finite.of_finite_tensorProduct_of_injective R M S hunit
  refine ⟨inferInstance, ?_⟩
  -- These stock structures retain the original semiring and additive-monoid parents.
  let : Ring S := Algebra.semiringToRing R
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let : AddCommGroup (S ⊗[R] M) := Module.addCommMonoidToAddCommGroup R
  let : Module.FinitePresentation S (S ⊗[R] M) :=
    Module.finitePresentation_of_projective S (S ⊗[R] M)
  let : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_finitePresentation_tensorProduct_of_injective R M S hunit
  obtain ⟨s, hs, hK⟩ := (inferInstance : Module.FinitePresentation R M).out
  -- Keep the generating subtype, so the presentation and all test objects have
  -- the required universe without changing carriers.
  let I := ↥s
  let F : Type (max uR uM) := I →₀ R
  let : AddCommGroup F := Module.addCommMonoidToAddCommGroup R
  let p : F →ₗ[R] M := Finsupp.linearCombination R ((↑) : I → M)
  let K : Submodule R F := LinearMap.ker p
  have hp : Function.Surjective p := by
    apply (_root_.span_range_eq_top_iff_surjective_finsuppLinearCombination
      (R := R) (v := ((↑) : I → M))).mp
    simpa only [Subtype.range_coe_subtype, Finset.setOfPred_mem] using hs
  obtain ⟨t, ht⟩ := (show K.FG from hK)
  let J := ↥t
  let e : I → F := fun i ↦ Finsupp.single i 1
  have hrepr (x : F) : ∑ i, x i • e i = x := by
    calc
      ∑ i, x i • e i = ∑ i, Finsupp.single i (x i) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finsupp.ext
        intro j
        change (x i • Finsupp.single i (1 : R)) j = _
        rw [Finsupp.smul_apply, Finsupp.single_apply, Finsupp.single_apply]
        split_ifs
        · exact mul_one _
        · exact mul_zero _
      _ = x := Finsupp.univ_sum_single x
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (p.baseChange S)
    (LinearMap.id : (S ⊗[R] M) →ₗ[S] S ⊗[R] M)
    (LinearMap.baseChange_surjective S hp)
  -- Restriction uses the stock tower for the original left-factor S-action.
  let σR : (S ⊗[R] M) →ₗ[R] S ⊗[R] F := σ.restrictScalars R
  have hσ_apply (x : S ⊗[R] M) : p.lTensor S (σR x) = x :=
    LinearMap.congr_fun hσ x
  let w : I → S ⊗[R] F := fun i ↦ σR ((1 : S) ⊗ₜ[R] p (e i))
  have hw₁ (i : I) : p.lTensor S (w i) = (1 : S) ⊗ₜ[R] p (e i) :=
    hσ_apply _
  have hw₂ (j : J) : ∑ i, (j : F) i • w i = 0 := by
    have hj : p (j : F) = 0 := by
      apply (LinearMap.mem_ker (f := p)).mp
      have hj : (j : F) ∈ Submodule.span R (↑t : Set F) :=
        Submodule.subset_span j.property
      rw [ht] at hj
      exact hj
    calc
      ∑ i, (j : F) i • w i =
          σR (∑ i, (j : F) i • ((1 : S) ⊗ₜ[R] p (e i))) := by
        simp only [map_sum, map_smul, w]
      _ = σR ((1 : S) ⊗ₜ[R] p (j : F)) := by
        congr 1
        calc
          ∑ i, (j : F) i • ((1 : S) ⊗ₜ[R] p (e i)) =
              (1 : S) ⊗ₜ[R] (∑ i, (j : F) i • p (e i)) := by
            simp only [TensorProduct.tmul_sum, TensorProduct.tmul_smul]
          _ = (1 : S) ⊗ₜ[R] p (∑ i, (j : F) i • e i) := by
            simp only [map_sum, map_smul]
          _ = _ := by rw [hrepr]
      _ = 0 := by rw [hj, TensorProduct.tmul_zero, map_zero]
  let X : Type (max uR uM) := I → F
  let Y : Type (max uR uM) := (I → M) × (J → F)
  let L : X →ₗ[R] Y :=
    (LinearMap.pi fun i ↦ p.comp (LinearMap.proj i)).prod
      (LinearMap.pi fun j ↦ ∑ i, (j : F) i • (LinearMap.proj i : X →ₗ[R] F))
  let d : Y := (fun i ↦ p (e i), 0)
  -- Only R-linear coordinates are needed: the auxiliary scalar in piRight is R,
  -- and its first tensor factor is the original R-module S.
  let eX := TensorProduct.piRight R R S (fun _ : I ↦ F)
  let eY := (TensorProduct.prodRight R R S (I → M) (J → F)).trans
    ((TensorProduct.piRight R R S (fun _ : I ↦ M)).prodCongr
      (TensorProduct.piRight R R S (fun _ : J ↦ F)))
  have hcoords (x : S ⊗[R] X) :
      eY (L.lTensor S x) =
        ((fun i ↦ p.lTensor S (eX x i)),
          fun j : J ↦ ∑ i, (j : F) i • eX x i) := by
    induction x using TensorProduct.inductionOn with
    | tmul a v =>
      apply Prod.ext
      · ext i
        rfl
      · ext j
        change a ⊗ₜ[R]
            ((∑ i, (j : F) i • (LinearMap.proj i : X →ₗ[R] F)) v) =
          ∑ i, (j : F) i • (a ⊗ₜ[R] v i)
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
          TensorProduct.tmul_sum, TensorProduct.tmul_smul]
    | add x y hx hy =>
      simp only [map_add, hx, hy, Prod.mk_add_mk, Pi.add_apply,
        smul_add, Finset.sum_add_distrib]
      rfl
  let z : S ⊗[R] X := eX.symm w
  have hz : L.lTensor S z = (1 : S) ⊗ₜ[R] d := by
    apply eY.injective
    rw [hcoords]
    simp only [z, eX.apply_symm_apply]
    apply Prod.ext
    · ext i
      exact hw₁ i
    · ext j
      change (∑ i, (j : F) i • w i) = (1 : S) ⊗ₜ[R] (0 : F)
      simpa only [TensorProduct.tmul_zero] using hw₂ j
  have hd : d ∈ LinearMap.range L := by
    apply (Submodule.one_tmul_mem_baseChange_iff_of_injective
      (R := R) (S := S) (M := Y) hunit (LinearMap.range L) d).mp
    change (1 : S) ⊗ₜ[R] d ∈
      LinearMap.range ((LinearMap.range L).subtype.baseChange S)
    refine ⟨L.rangeRestrict.lTensor S z, ?_⟩
    change (LinearMap.range L).subtype.lTensor S (L.rangeRestrict.lTensor S z) = _
    rw [← LinearMap.lTensor_comp_apply, LinearMap.subtype_comp_rangeRestrict]
    exact hz
  obtain ⟨v, hv⟩ := hd
  have hv₁ (i : I) : p (v i) = p (e i) :=
    congrArg (fun y : Y ↦ y.1 i) hv
  have hv₂ (j : J) : ∑ i, (j : F) i • v i = 0 := by
    have hj := congrArg (fun y : Y ↦ y.2 j) hv
    change (∑ i, (j : F) i • (LinearMap.proj i : X →ₗ[R] F)) v = 0 at hj
    simpa only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply] using hj
  let W : F →ₗ[R] F := Finsupp.linearCombination R v
  have hWe (i : I) : W (e i) = v i := by
    exact (Finsupp.linearCombination_single R (v := v) 1 i).trans (one_smul R (v i))
  have hpW : p.comp W = p := by
    apply LinearMap.ext
    intro x
    change p (W x) = p x
    calc
      p (W x) = p (W (∑ i, x i • e i)) := congrArg (fun y ↦ p (W y)) (hrepr x).symm
      _ = ∑ i, x i • p (e i) := by simp only [map_sum, map_smul, hWe, hv₁]
      _ = p (∑ i, x i • e i) := by simp only [map_sum, map_smul]
      _ = p x := congrArg p (hrepr x)
  have hKW : K ≤ LinearMap.ker W := by
    rw [← ht]
    apply Submodule.span_le.mpr
    intro x hx
    change W x = 0
    calc
      W x = W (∑ i, x i • e i) := congrArg W (hrepr x).symm
      _ = ∑ i, x i • v i := by simp only [map_sum, map_smul, hWe]
      _ = 0 := hv₂ ⟨x, hx⟩
  let q : M →ₗ[R] F := (K.liftQ W hKW).comp
    (p.quotKerEquivOfSurjective hp).symm.toLinearMap
  have hq (x : F) : q (p x) = W x := by simp [q, K]
  apply Module.Projective.of_split q p
  apply LinearMap.ext
  intro m
  obtain ⟨x, rfl⟩ := hp m
  rw [LinearMap.comp_apply, hq]
  exact LinearMap.congr_fun hpW x

end Module
