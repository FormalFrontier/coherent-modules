/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Ideal.Maps

/-!
# Extension of a product power over commutative semirings

The generalized extension formula for powers combines with Mathlib's existing
commutative product and power formulas to distribute extension over the powers
of both factors. This includes exponent zero and uses independent coefficient
universes.
-/

universe u v

example {A : Type u} {B : Type v} [CommSemiring A] [CommSemiring B]
    (f : A →+* B) (I J : Ideal A) (n : ℕ) :
    Ideal.map f ((I * J) ^ n) = Ideal.map f (I ^ n) * Ideal.map f (J ^ n) := by
  rw [Ideal.map_pow_of_isTwoSided, Ideal.map_mul, mul_pow, ← Ideal.map_pow,
    ← Ideal.map_pow]
