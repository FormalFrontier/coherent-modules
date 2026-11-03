/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.Dual.Nondegenerate
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# A tensor–dual criterion for a Frobenius functional

For a finite-dimensional algebra `A` over a field `K`, a subspace `C` of the
ordinary dual with an equivalence `C ⊗[K] A ≃ₗ[K] Module.Dual K A` whose value
on `c ⊗ₜ a` is `x ↦ c (a * x)` yields a nondegenerate multiplication pairing.
The algebra may be noncommutative or zero. No finiteness hypothesis on `C`
is needed: it is a subspace of the finite-dimensional dual.

The proof uses finite-dimensional duality and tensor dimensions from Mathlib,
then the nondegeneracy criterion for bijective self-pairings.
-/

@[expose] public section

universe uK uA

open scoped TensorProduct

namespace Module.Dual

/-- A tensor equivalence with the multiplication readback produces a Frobenius
functional: the multiplication pairing is nondegenerate in both arguments.
The algebra is allowed to be zero or noncommutative. -/
theorem exists_nondegenerate_mul_of_tensorProduct_equiv
    {K : Type uK} {A : Type uA}
    [Field K] [Semiring A] [Algebra K A] [Module.Finite K A]
    (C : Submodule K (Module.Dual K A))
    (e : C ⊗[K] A ≃ₗ[K] Module.Dual K A)
    (he : ∀ (c : C) (a x : A),
      (e (c ⊗ₜ[K] a)) x = (c : Module.Dual K A) (a * x)) :
    ∃ φ : A →ₗ[K] K, ((LinearMap.mul K A).compr₂ φ).Nondegenerate := by
  classical
  by_cases hA : Subsingleton A
  · let _ := hA
    refine ⟨0, LinearMap.nondegenerate_of_bijective _ ⟨?_, ?_⟩⟩
    · intro a b _
      exact Subsingleton.elim a b
    · intro φ
      refine ⟨0, ?_⟩
      ext x
      have hx : x = 0 := Subsingleton.elim x 0
      simp [hx]
  · let _ : Nontrivial A := not_subsingleton_iff_nontrivial.mp hA
    -- The given field-module structures supply additive inverses without
    -- changing the original additions or scalar actions.
    let _ : AddCommGroup A := Module.addCommMonoidToAddCommGroup K
    let _ : AddCommGroup C := Module.addCommMonoidToAddCommGroup K
    have hdim : Module.finrank K C * Module.finrank K A = Module.finrank K A := by
      rw [← Module.finrank_tensorProduct, e.finrank_eq, Subspace.dual_finrank_eq]
    have hpos : 0 < Module.finrank K A := Module.finrank_pos
    have hC : Module.finrank K C = 1 := by
      apply mul_right_cancel₀ (ne_of_gt hpos)
      simpa only [one_mul] using hdim
    let q : K ≃ₗ[K] C := LinearEquiv.ofFinrankEq K C (by simpa using hC.symm)
    let f : A ≃ₗ[K] Module.Dual K A :=
      ((TensorProduct.lid K A).symm.trans
        (TensorProduct.congr q (LinearEquiv.refl K A))).trans e
    refine ⟨(q 1 : Module.Dual K A), LinearMap.nondegenerate_of_bijective _ ?_⟩
    have hf : (LinearMap.mul K A).compr₂ (q 1 : Module.Dual K A) = f.toLinearMap := by
      ext a x
      simp [f, he]
    rw [hf]
    exact f.bijective

end Module.Dual
