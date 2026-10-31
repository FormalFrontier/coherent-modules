/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Ideal.Quotient.Annihilator

/-!
# Compatibility with the quotient action on an additive group

The faithfulness theorem uses the group structure induced by the ring-module
structure. It also applies to the quotient action defined using a pre-existing
additive group structure, without transporting or replacing scalar multiplication.
-/

universe uR uM

/-- Recover the quotient action formed with the original additive group structure. -/
private theorem faithful_quotient_annihilator
    (R : Type uR) (M : Type uM) [Ring R] [AddCommGroup M] [Module R M] :
    @FaithfulSMul (R ⧸ Module.annihilator R M) M
      (Module.quotientAnnihilator (R := R) (M := M)).toSMul :=
  Module.quotientAnnihilator_faithfulSMul R M
