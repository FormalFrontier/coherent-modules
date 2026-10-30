/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules

/-!
# Faithfully flat compatibility for finite-cokernel surjectivity

On maps with finitely generated cokernel, the arbitrary-factor surjectivity
criterion has the same tensor map and conclusion as
`Module.FaithfullyFlat.lTensor_surjective_iff_surjective`. The latter applies to
all maps. Here the new criterion is applied using only the proper maximal-ideal
images supplied by faithful flatness.
-/

@[expose] public section

universe uR uP uM uN

example
    {R : Type uR} [CommRing R]
    {P : Type uP} [AddCommGroup P] [Module R P] [Module.FaithfullyFlat R P]
    {M : Type uM} [AddCommGroup M] [Module R M]
    {N : Type uN} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) [Module.Finite R (N ⧸ LinearMap.range f)] :
    Function.Surjective (f.lTensor P) ↔ Function.Surjective f := by
  exact LinearMap.lTensor_surjective_iff_surjective_of_finite_cokernel f
    (fun _ hm ↦ Module.FaithfullyFlat.submodule_ne_top hm)
