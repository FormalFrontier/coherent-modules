/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.RingTheory.Ideal.AdicLocality

/-!
# Adic cofinality from distinguished neighbourhoods of the closed locus

The descent criteria for full and finite-submodule adic cofinality give stage
inclusions on the original finite `R`-module, in a universe independent of `R`.
The distinguished opens need only cover the closed locus of `I`. The full
condition applies to arbitrary submodules; only the finite-submodule condition
requires finite generation of the submodule.
-/

universe uR uM

example
    {R : Type uR} [CommRing R] (I : Ideal R) (s : Set R)
    (hcover : I ⊔ Ideal.span s = ⊤)
    (hlocal : ∀ f ∈ s,
      (I.map (algebraMap R (Localization.Away f))).HasSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (n : ℕ) :
    ∃ m : ℕ, N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N :=
  ((Ideal.hasSubmoduleAdicCofinality_iff_forall_map_away I s hcover).mpr hlocal).cofinal N n

example
    {R : Type uR} [CommRing R] (I : Ideal R) (s : Set R)
    (hcover : I ⊔ Ideal.span s = ⊤)
    (hlocal : ∀ f ∈ s,
      (I.map (algebraMap R (Localization.Away f))).HasFiniteSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (hN : N.FG) (n : ℕ) :
    ∃ m : ℕ, N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N :=
  ((Ideal.hasFiniteSubmoduleAdicCofinality_iff_forall_map_away I s hcover).mpr hlocal).cofinal
    N hN n
