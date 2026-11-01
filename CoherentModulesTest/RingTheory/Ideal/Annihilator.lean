/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.RingTheory.Ideal.Annihilator

/-!
# Same-scalar specializations of annihilator transport

The semilinear transport results recover `LinearMap.annihilator_le_of_surjective`,
`LinearMap.annihilator_le_of_injective`, and `LinearEquiv.annihilator_eq` by specializing the
scalar homomorphism to the identity.
-/

universe uR uM uN

variable {R : Type uR} {M : Type uM} {N : Type uN}
    [Semiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

private theorem annihilator_le_of_surjective_linearMap (f : M →ₗ[R] N)
    (hf : Function.Surjective f) :
    Module.annihilator R M ≤ Module.annihilator R N := by
  simpa only [Ideal.comap_id] using f.annihilator_le_comap_of_surjective hf

private theorem annihilator_le_of_injective_linearMap (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Module.annihilator R N ≤ Module.annihilator R M := by
  simpa only [Ideal.comap_id] using f.comap_annihilator_le_of_injective hf

private theorem annihilator_eq_of_linearEquiv (e : M ≃ₗ[R] N) :
    Module.annihilator R M = Module.annihilator R N := by
  simpa only [Ideal.comap_id] using
    e.toLinearMap.annihilator_eq_comap_of_bijective e.bijective
