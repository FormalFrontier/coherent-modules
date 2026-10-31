/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Faithfulness of the annihilator-quotient action

A module over a ring is faithful over the quotient by its annihilator.
The scalar action is the one provided by `Module.quotientAnnihilator`, using the
additive group structure induced by the ring-module structure.
Neither commutativity nor finiteness is required.
-/

@[expose] public section

universe uR uM

namespace Module

/-- The action of the quotient by the annihilator on a module, given by
`Module.quotientAnnihilator`, is faithful. -/
theorem quotientAnnihilator_faithfulSMul
    (R : Type uR) (M : Type uM) [Ring R] [AddCommMonoid M] [Module R M] :
    @FaithfulSMul (R ⧸ annihilator R M) M
      (@quotientAnnihilator R M _ (Module.addCommMonoidToAddCommGroup R) _).toSMul := by
  let _ : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let _ := quotientAnnihilator (R := R) (M := M)
  refine ⟨fun {a b} h ↦ ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply Ideal.Quotient.eq.mpr
  apply mem_annihilator.mpr
  intro m
  have hab : a • m = b • m := by
    simpa only [(isTorsionBySet_annihilator R M).mk_smul] using h m
  rw [sub_eq_add_neg, add_smul, hab, ← add_smul, add_neg_cancel, zero_smul]

end Module
