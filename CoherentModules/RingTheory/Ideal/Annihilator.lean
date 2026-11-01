/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Ideal.Maps

/-!
# Annihilators and semilinear maps

A surjective semilinear map carries annihilating scalars to annihilating scalars. For an
injective semilinear map, a scalar whose image annihilates the target annihilates the source.
For a bijective semilinear map, the source annihilator is the comap of the target annihilator.

These results generalize `LinearMap.annihilator_le_of_surjective`,
`LinearMap.annihilator_le_of_injective`, and `LinearEquiv.annihilator_eq` in
`Mathlib.RingTheory.Ideal.Maps`. The proofs follow their elementwise arguments.
-/

@[expose] public section

universe uR uS uM uN

namespace LinearMap

variable {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN}
    [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module S N] {ρ : R →+* S}

/-- Along a surjective semilinear map, every scalar annihilating the source has image
annihilating the target. -/
theorem annihilator_le_comap_of_surjective (f : M →ₛₗ[ρ] N)
    (hf : Function.Surjective f) :
    Module.annihilator R M ≤ Ideal.comap ρ (Module.annihilator S N) := by
  intro r hr
  rw [Module.mem_annihilator] at hr
  rw [Ideal.mem_comap, Module.mem_annihilator]
  intro n
  obtain ⟨m, rfl⟩ := hf n
  rw [← f.map_smulₛₗ, hr, f.map_zero]

/-- Along an injective semilinear map, a scalar whose image annihilates the target
annihilates the source. -/
theorem comap_annihilator_le_of_injective (f : M →ₛₗ[ρ] N)
    (hf : Function.Injective f) :
    Ideal.comap ρ (Module.annihilator S N) ≤ Module.annihilator R M := by
  intro r hr
  rw [Ideal.mem_comap, Module.mem_annihilator] at hr
  rw [Module.mem_annihilator]
  intro m
  apply hf
  rw [f.map_smulₛₗ, hr, f.map_zero]

/-- A bijective semilinear map identifies the source annihilator with the comap of the
target annihilator. -/
theorem annihilator_eq_comap_of_bijective (f : M →ₛₗ[ρ] N)
    (hf : Function.Bijective f) :
    Module.annihilator R M = Ideal.comap ρ (Module.annihilator S N) :=
  (f.annihilator_le_comap_of_surjective hf.2).antisymm
    (f.comap_annihilator_le_of_injective hf.1)

end LinearMap
