/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents

The module-length formalization in Mathlib carries the notice:
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.Length

/-!
# Module length under semilinear bijections

A bijective semilinear map over a surjective ring homomorphism preserves module
length. The scalar rings may be noncommutative, and the scalar homomorphism need
not be injective. Both finite and infinite lengths are included.

The proof uses Mathlib's submodule map/comap order isomorphism for the given
semilinear map, without changing either module structure.

## References

* Mathlib's `Submodule.orderIsoMapComapOfBijective` identifies the submodule lattices.
* Andrew Yang's module-length formalization provides `Module.coe_length`; its
  `LinearEquiv.length_eq` uses the same reduction to
  `Order.krullDim_eq_of_orderIso` from Mathlib's Krull-dimension formalization.
-/

@[expose] public section

universe uR uS uM uN

namespace LinearMap

/-- A bijective semilinear map over a surjective scalar ring homomorphism preserves
module length, including infinite length. The scalar homomorphism need not be
injective. -/
theorem length_eq_of_bijective
    {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN}
    [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N] {σ : R →+* S}
    (g : M →ₛₗ[σ] N) (hσ : Function.Surjective σ) (hg : Function.Bijective g) :
    Module.length R M = Module.length S N := by
  let : RingHomSurjective σ := ⟨hσ⟩
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective g hg)]

end LinearMap
