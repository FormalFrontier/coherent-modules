/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.RingTheory.Ideal.AdicCompatibility
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Finiteness.Prod

/-!
# Adic cofinality over a diagonal product algebra

Both cofinality conditions extend along the diagonal algebra map `R → R × R`.
The product algebra is finite as an `R`-module. For a nontrivial ring the diagonal
map is not surjective, so these uses are not instances of quotient transport.
The resulting cofinality applies in an independent module universe.
-/

universe uR uM

example
    {R : Type uR} [CommRing R] (I : Ideal R) (hI : I.HasSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module (R × R) M] [Module.Finite (R × R) M]
    (N : Submodule (R × R) M) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ (((I.map (algebraMap R (R × R))) ^ m) • (⊤ : Submodule (R × R) M)) ≤
        ((I.map (algebraMap R (R × R))) ^ n) • N :=
  (hI.map (S := R × R)).cofinal N

example
    {R : Type uR} [CommRing R] (I : Ideal R) (hI : I.HasFiniteSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module (R × R) M] [Module.Finite (R × R) M]
    (N : Submodule (R × R) M) (hN : N.FG) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ (((I.map (algebraMap R (R × R))) ^ m) • (⊤ : Submodule (R × R) M)) ≤
        ((I.map (algebraMap R (R × R))) ^ n) • N :=
  (hI.map (S := R × R)).cofinal N hN
