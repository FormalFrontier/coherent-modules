/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.RingTheory.Ideal.AdicCompatibility
import Mathlib.Algebra.Algebra.Prod
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Adic cofinality under finite algebras and localization

Both cofinality conditions extend along the diagonal algebra map `R → R × R`.
The product algebra is finite as an `R`-module. For a nontrivial ring the diagonal
map is not surjective, so these uses are not instances of quotient transport.
The resulting cofinality applies in an independent module universe.

The localization uses below retain the given target module action. The full
condition is applied after localization away from an arbitrary element; the
finite-submodule condition is applied to an abstract localization algebra in an
independent universe. Neither use assumes the localization is module-finite.
-/

universe uR uA uM

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

example
    {R : Type uR} [CommRing R] (I : Ideal R) (hI : I.HasSubmoduleAdicCofinality)
    (s : R) {M : Type uM} [AddCommGroup M] [Module (Localization.Away s) M]
    [Module.Finite (Localization.Away s) M] (N : Submodule (Localization.Away s) M) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ (((I.map (algebraMap R (Localization.Away s))) ^ m) •
        (⊤ : Submodule (Localization.Away s) M)) ≤
        ((I.map (algebraMap R (Localization.Away s))) ^ n) • N :=
  (hI.map_of_isLocalization (A := Localization.Away s) (Submonoid.powers s)).cofinal N

example
    {R : Type uR} [CommRing R] {A : Type uA} [CommRing A] [Algebra R A]
    (I : Ideal R) (hI : I.HasFiniteSubmoduleAdicCofinality)
    (S : Submonoid R) [IsLocalization S A]
    {M : Type uM} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Submodule A M) (hN : N.FG) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ (((I.map (algebraMap R A)) ^ m) • (⊤ : Submodule A M)) ≤
        ((I.map (algebraMap R A)) ^ n) • N :=
  (hI.map_of_isLocalization (A := A) S).cofinal N hN
