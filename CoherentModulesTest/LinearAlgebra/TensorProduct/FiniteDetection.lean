/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Finite tensor detection clients

The finite faithfully-flat specialization has the same conclusion and canonical
actions as `Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right` on finite
modules; that theorem still applies to arbitrary modules. The residue-field
specialization is exactly the proposition, action and left-residue tensor
orientation of `IsLocalRing.subsingleton_tensorProduct`, from Andrew Yang's
formalization of finite modules over local rings. Both clients instead apply the
general finite detection theorem after independently establishing its ideal premise.

The countable direct sum of residue fields supplies a coefficient module without
any ring, flatness, faithfulness or finiteness premise. Its maximal ideal acts by
zero componentwise, and a summand witnesses nontriviality.
-/

@[expose] public section

open scoped TensorProduct DirectSum

universe u v w

namespace CoherentModulesTest.TensorProduct.FiniteDetection

/-- On finite modules the arbitrary-factor criterion recovers the faithfully-flat
triviality criterion, using only its maximal-ideal proper-image hypothesis. -/
theorem faithfullyFlat_finite
    {R : Type u} {P : Type v} {M : Type w}
    [CommRing R] [AddCommGroup P] [Module R P] [Module.FaithfullyFlat R P]
    [AddCommMonoid M] [Module R M] [Module.Finite R M] :
    Subsingleton (P ⊗[R] M) ↔ Subsingleton M := by
  exact Module.subsingleton_tensorProduct_iff_of_finite
    (fun _ hm ↦ Module.FaithfullyFlat.submodule_ne_top hm)

private theorem residue_smul_eq_zero
    {R : Type u} [CommRing R] [IsLocalRing R]
    {r : R} (hr : r ∈ IsLocalRing.maximalIdeal R) (x : IsLocalRing.ResidueField R) :
    r • x = 0 := by
  rw [Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq,
    (IsLocalRing.residue_eq_zero_iff r).mpr hr, zero_mul]

/-- The general criterion specializes to the same proposition and quotient action
as `IsLocalRing.subsingleton_tensorProduct`, without using that theorem. -/
theorem localResidue_finite
    {R : Type u} {M : Type w} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Subsingleton (IsLocalRing.ResidueField R ⊗[R] M) ↔ Subsingleton M := by
  apply Module.subsingleton_tensorProduct_iff_of_finite
  intro m hm
  rw [IsLocalRing.eq_maximalIdeal hm]
  have hzero : IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R (IsLocalRing.ResidueField R)) = ⊥ := by
    apply le_antisymm ?_ bot_le
    exact Submodule.smul_le.mpr fun r hr x _ ↦
      (Submodule.mem_bot R).mpr (residue_smul_eq_zero hr x)
  rw [hzero]
  exact bot_ne_top

/-- Tensoring a finite module with the countable direct sum of residue fields
reflects the zero module, with no flatness or finiteness premise on this sum. -/
theorem subsingleton_of_residueDirectSum_tensor
    {R : Type u} {M : Type w} [CommRing R] [IsLocalRing R]
    [AddCommMonoid M] [Module R M] [Module.Finite R M]
    (h : Subsingleton ((⨁ _ : ℕ, IsLocalRing.ResidueField R) ⊗[R] M)) :
    Subsingleton M := by
  have : Nontrivial (⨁ _ : ℕ, IsLocalRing.ResidueField R) :=
    Function.Injective.nontrivial
      (DirectSum.of_injective (β := fun _ : ℕ ↦ IsLocalRing.ResidueField R) 0)
  apply (Module.subsingleton_tensorProduct_iff_of_finite ?_).mp h
  intro m hm
  rw [IsLocalRing.eq_maximalIdeal hm]
  have hzero : IsLocalRing.maximalIdeal R •
      (⊤ : Submodule R (⨁ _ : ℕ, IsLocalRing.ResidueField R)) = ⊥ := by
    apply le_antisymm ?_ bot_le
    refine Submodule.smul_le.mpr fun r hr x _ ↦ (Submodule.mem_bot R).mpr ?_
    ext n
    exact residue_smul_eq_zero hr (x n)
  rw [hzero]
  exact bot_ne_top

end CoherentModulesTest.TensorProduct.FiniteDetection
