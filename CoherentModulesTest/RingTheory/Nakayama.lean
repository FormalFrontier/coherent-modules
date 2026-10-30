/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules

/-!
# Annihilator criteria and finite tensor detection

The first check recovers the proposition of Mathlib's
`Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator` from the comaximality
criterion, under exactly its hypotheses. The second uses the annihilator bound
on finite coefficients as input to tensor detection of a finite zero module.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace CoherentModulesTest.Nakayama

/-- The annihilator criterion recovers Nakayama properness under relative
Jacobson containment, with the equality orientation of Mathlib's theorem. -/
theorem top_ne_ideal_smul
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Nontrivial M] [Module.Finite R M] {I : Ideal R}
    (h : I ≤ (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) ≠ I • ⊤ := by
  intro heq
  have hsup : I ⊔ Module.annihilator R M = ⊤ := by
    simpa only [Submodule.annihilator_top] using
      (Module.Finite.fg_top.ideal_smul_eq_self_iff_sup_annihilator_eq_top I).mp heq.symm
  have hJac : (Module.annihilator R M).jacobson = ⊤ := by
    apply top_unique
    rw [← hsup]
    exact sup_le h Ideal.le_jacobson
  exact not_subsingleton M (Module.annihilator_eq_top_iff.mp
    (Ideal.jacobson_eq_top_iff.mp hJac))

/-- A Jacobson bound on the annihilator of finite coefficients supplies the
maximal-ideal input for detecting that a finite module is zero by tensoring. -/
theorem subsingleton_of_tensor
    {R : Type u} {P : Type v} {M : Type w}
    [CommRing R] [AddCommMonoid P] [Module R P] [Module.Finite R P]
    [AddCommMonoid M] [Module R M] [Module.Finite R M]
    (hA : Module.annihilator R P ≤ Ideal.jacobson (⊥ : Ideal R))
    (hzero : Subsingleton (P ⊗[R] M)) : Subsingleton M := by
  have hP : ∀ m : Ideal R, m.IsMaximal → m • (⊤ : Submodule R P) ≠ ⊤ :=
    Module.forall_maximal_smul_top_ne_top_iff_annihilator_le_jacobson.mpr hA
  exact (Module.subsingleton_tensorProduct_iff_of_finite hP).mp hzero

end CoherentModulesTest.Nakayama
