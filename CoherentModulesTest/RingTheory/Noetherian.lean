/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Scalar clearing and surjective specializations

The ideal and ring conclusions recover the familiar surjective cases.
For semimodules, the range equivalence identifies clearing with Mathlib's
surjective criterion when the scalar homomorphism is surjective. Carrier
universes remain independent and commutativity is not required.
-/

@[expose] public section

universe u v w x

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S]

example (f : R →+* S) (hf : Function.Surjective f) (I : Ideal S) :
    (I.comap f).map f = I :=
  Ideal.map_comap_eq_of_unit_mul_mem_range f
    (f.exists_unit_mul_mem_range_of_surjective hf) I

example [IsNoetherianRing R] (f : R →+* S) (hf : Function.Surjective f) :
    IsNoetherianRing S :=
  isNoetherianRing_of_unit_mul_mem_range f
    (f.exists_unit_mul_mem_range_of_surjective hf)

-- At Mathlib's scalar-surjectivity hypothesis, the clearing equivalence
-- recovers ascent from its `isNoetherian_of_surjective` theorem.
example {M : Type w} {N : Type x} [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module S N] {φ : R →+* S} [RingHomSurjective φ]
    (f : M →ₛₗ[φ] N)
    (hclear : ∀ n : N, ∃ m : M, ∃ a b : S, b * a = 1 ∧ f m = a • n)
    [IsNoetherian R M] : IsNoetherian S N :=
  isNoetherian_of_surjective f (f.range_eq_top_iff_left_inv_smul_mem_range.mpr hclear)
