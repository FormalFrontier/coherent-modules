/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Order.Atoms

/-!
# The projection kernel as a coatom

The left-ideal classifier transports the coatom given by the coefficient lattice's
internal top to the projection kernel. The adjoined top remains the whole extension,
even when the coefficient module is zero. This uses Mathlib's coatom transport and
`WithTop` order API without unfolding the classifier.
-/

universe u v

namespace TrivSqZeroExt

/-- The projection kernel is a maximal proper left ideal, for the given commuting actions. -/
private theorem isCoatom_ker_fstHom
    (D : Type u) (M : Type v) [DivisionSemiring D] [AddCommGroup M]
    [Module D M] [Module Dᵐᵒᵖ M] [SMulCommClass D Dᵐᵒᵖ M] :
    IsCoatom (RingHom.ker (fstHom ℕ D M : TrivSqZeroExt D M →+* D)) := by
  rw [← idealOrderIsoWithTop_symm_coe_top D M, OrderIso.isCoatom_iff]
  exact ⟨WithTop.coe_ne_top, fun _ h ↦ WithTop.coe_top_lt.mp h⟩

end TrivSqZeroExt
