/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.NormNum

/-!
# Rational base change does not reflect faithful flatness

The maximal ideal `(2)` of the integers extends to the unit ideal of the rationals.
The universal characterization therefore rules out reflection of faithful flatness
on all flat integer modules, in every test universe. This uses the converse through
the library's public entry point, rather than assuming a scalar-flatness or
surjectivity criterion.
-/

@[expose] public section

open scoped TensorProduct

universe w

namespace CoherentModulesTest.Flat.BaseChange

/-- Even though rational scalar extension is flat, it fails to reflect faithful
flatness on all flat integer modules in any test universe. -/
theorem integerRationalNotUniversalReflection :
    ¬ ∀ (M : Type w) [AddCommGroup M] [Module ℤ M],
    Module.Flat ℤ M →
      (Module.FaithfullyFlat ℤ M ↔ Module.FaithfullyFlat ℚ (ℚ ⊗[ℤ] M)) := by
  intro h
  have hmax :=
    (Algebra.map_maximal_ne_top_iff_forall_faithfullyFlat_baseChange
      (R := ℤ) (S := ℚ)).mpr h
  have hmap : (Ideal.span ({2} : Set ℤ)).map (algebraMap ℤ ℚ) = ⊤ := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
    norm_num
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hmax (Ideal.span ({2} : Set ℤ)) (Int.ideal_span_isMaximal_of_prime 2) hmap

end CoherentModulesTest.Flat.BaseChange
