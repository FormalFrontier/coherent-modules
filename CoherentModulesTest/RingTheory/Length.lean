/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.RingTheory.Length

/-!
# Module length along a surjective algebra map

The identity additive map, with its algebra-map semilinearity, specializes
`LinearMap.length_eq_of_bijective` to the equality of
`Module.length_eq_of_surjective` under exactly that theorem's hypotheses.
-/

universe uR uS uM

private theorem length_eq_of_surjective_specialization
    {R : Type uR} {S : Type uS} {M : Type uM}
    [Ring R] [CommRing S] [AddCommGroup M]
    [Module R M] [Algebra S R] [Module S M] [IsScalarTower S R M]
    (h : Function.Surjective (algebraMap S R)) :
    Module.length S M = Module.length R M := by
  let f : M →ₛₗ[algebraMap S R] M := ⟨AddHom.id M, by simp⟩
  exact LinearMap.length_eq_of_bijective f h Function.bijective_id
