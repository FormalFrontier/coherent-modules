/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.RingTheory.TwoSidedIdeal.Atoms
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Simple quotients from two-sided ideal coatomicity

Every nontrivial ring has a nontrivial simple quotient. The quotient and its
surjective unital homomorphism are the ring congruence quotient and quotient map.
The proof combines coatomicity with Mathlib's order and congruence correspondence APIs.
-/

example (R : Type*) [Ring R] [Nontrivial R] :
    ∃ M : TwoSidedIdeal R, Nontrivial M.ringCon.Quotient ∧
      IsSimpleRing M.ringCon.Quotient ∧ Function.Surjective M.ringCon.mk' := by
  let := TwoSidedIdeal.isCoatomic R
  obtain ⟨M, hM⟩ := IsCoatomic.exists_coatom (TwoSidedIdeal R)
  have hC : IsCoatom M.ringCon := TwoSidedIdeal.orderIsoRingCon.isCoatom_iff M |>.mpr hM
  let : IsSimpleOrder (Set.Ici M.ringCon) := Set.isSimpleOrder_Ici_iff_isCoatom.mpr hC
  let : IsSimpleOrder (RingCon M.ringCon.Quotient) :=
    (RingCon.correspondence (c := M.ringCon)).symm.isSimpleOrder
  refine ⟨M, RingCon.nontrivial_quotient.mpr hC.1, ⟨?_⟩, M.ringCon.mk'_surjective⟩
  exact TwoSidedIdeal.orderIsoRingCon.isSimpleOrder
