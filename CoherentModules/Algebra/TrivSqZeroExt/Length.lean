/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.Length

/-!
# Length of a trivial square-zero extension

For a division ring `D` and a coefficient module `M` with commuting left and right
`D`-actions, the regular left module of `TrivSqZeroExt D M` has length
`Module.length D M + 1`. The formula takes values in `ℕ∞` and does not require `M`
to be finite-dimensional. If `M` is finite-dimensional, the extension's length is
the finrank of `M` plus one.

The coefficient submodule lattice is nonempty even when `M` is zero. Its internal
top corresponds to the projection kernel, whereas the adjoined top corresponds
to the whole extension.

## References

The proof uses `TrivSqZeroExt.idealOrderIsoWithTop` and Mathlib's
`Order.krullDim_eq_of_orderIso`, `Order.krullDim_WithTop`, `Module.coe_length`,
and `Module.length_eq_finrank`.
-/

@[expose] public section

universe uD uM

namespace TrivSqZeroExt

variable {D : Type uD} {M : Type uM} [DivisionRing D] [AddCommGroup M]
  [Module D M] [Module Dᵐᵒᵖ M] [SMulCommClass D Dᵐᵒᵖ M]

/-- The length of the regular left module of a trivial square-zero extension over
a division ring is one more than the length of its coefficient module, including
infinite lengths. -/
theorem length :
    Module.length (TrivSqZeroExt D M) (TrivSqZeroExt D M) = Module.length D M + 1 := by
  apply WithBot.coe_injective
  rw [WithBot.coe_add, WithBot.coe_one, Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (idealOrderIsoWithTop D M), Order.krullDim_WithTop]

/-- For finite-dimensional coefficients, the length of the regular left module of
a trivial square-zero extension is the coefficient finrank plus one. -/
theorem length_eq_finrank_add_one [Module.Finite D M] :
    Module.length (TrivSqZeroExt D M) (TrivSqZeroExt D M) =
      (Module.finrank D M : ℕ∞) + 1 := by
  rw [TrivSqZeroExt.length, Module.length_eq_finrank]

end TrivSqZeroExt
