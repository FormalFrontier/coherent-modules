/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Faithful flatness from a surjective linear map

A flat module surjecting onto a faithfully flat module is faithfully flat.
The ring and both module carriers may lie in independent universes.

## Proof approach

Mapping an equality `I • ⊤ = ⊤` along the surjection gives the same equality
in the target. The target's faithful flatness forces `I = ⊤`; combining this
with the source's flatness proves faithful flatness of the source.

## References

The proof uses Mathlib's ideal-smul criterion for faithful flatness,
`Submodule.map_smul''`, `Submodule.map_top` and `LinearMap.range_eq_top`.
-/

@[expose] public section

universe u v w

namespace Module.FaithfullyFlat

/-- A flat source module is faithfully flat if it admits a surjective linear map
onto a faithfully flat target module over the same commutative ring. -/
theorem of_surjective
    {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Flat R M] [Module.FaithfullyFlat R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.FaithfullyFlat R M := by
  apply (Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top R M).mpr
  refine ⟨inferInstance, ?_⟩
  intro I hI
  apply ((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top R N).mp inferInstance).2 I
  simpa only [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr hf] using congrArg (Submodule.map f) hI

end Module.FaithfullyFlat
