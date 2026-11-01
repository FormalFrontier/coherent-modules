/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Ideal.AdicProducts

/-!
# Finite-product adic cofinality on the original module

For an arbitrary ideal of a finite dependent product, cofinality of its
projection images gives a stage inclusion on every submodule of the original
finite module. The binary product-ideal example uses the finite-submodule
condition, so only its submodule must additionally be finitely generated.

The index, coefficient and module universes are independent, as are the two
binary coefficient universes. Neither example replaces the given scalar action
or assumes the ambient module is finite over a component ring.
-/

universe uι uR uS uM

example
    {ι : Type uι} [Finite ι] {R : ι → Type uR} [∀ i, CommRing (R i)]
    (I : Ideal (Π i, R i))
    (hI : ∀ i, (I.map (Pi.evalRingHom R i)).HasSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module (Π i, R i) M]
    [Module.Finite (Π i, R i) M] (N : Submodule (Π i, R i) M) (n : ℕ) :
    ∃ m : ℕ, N ⊓ ((I ^ m) • (⊤ : Submodule (Π i, R i) M)) ≤ (I ^ n) • N :=
  ((Ideal.hasSubmoduleAdicCofinality_iff_forall_map_evalRingHom I).mpr hI).cofinal N n

example
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S)
    (hI : I.HasFiniteSubmoduleAdicCofinality)
    (hJ : J.HasFiniteSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module (R × S) M] [Module.Finite (R × S) M]
    (N : Submodule (R × S) M) (hN : N.FG) (n : ℕ) :
    ∃ m : ℕ,
      N ⊓ (((I.prod J) ^ m) • (⊤ : Submodule (R × S) M)) ≤ ((I.prod J) ^ n) • N :=
  ((Ideal.hasFiniteSubmoduleAdicCofinality_prod_iff I J).mpr ⟨hI, hJ⟩).cofinal N hN n
