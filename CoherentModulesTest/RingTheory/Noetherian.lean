/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Noetherian

/-!
# Surjective specializations of unit clearing

The ideal and Noetherian conclusions recover the familiar surjective cases,
with independent source and target universes and without commutativity.
-/

@[expose] public section

universe u v

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S]

example (f : R →+* S) (hf : Function.Surjective f) (I : Ideal S) :
    (I.comap f).map f = I :=
  Ideal.map_comap_eq_of_unit_mul_mem_range f
    (f.exists_unit_mul_mem_range_of_surjective hf) I

example [IsNoetherianRing R] (f : R →+* S) (hf : Function.Surjective f) :
    IsNoetherianRing S :=
  isNoetherianRing_of_unit_mul_mem_range f
    (f.exists_unit_mul_mem_range_of_surjective hf)
