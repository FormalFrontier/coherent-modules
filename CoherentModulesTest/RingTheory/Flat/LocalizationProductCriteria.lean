/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModulesTest.RingTheory.Flat.LocalizationProduct
public import CoherentModulesTest.RingTheory.Flat.LocalizationProductInfinite
public import CoherentModules.RingTheory.Flat.Localization

/-!
# Finitely generated ideal detection in localization products

For the ring of sequences `ℕ → ZMod 2`, the product of the localizations at the
coordinate idempotents is faithfully flat. The arbitrary-submonoid product
criterion implies that every finitely generated proper ideal omits some
coordinate idempotent. Consequently, the proper ideal spanned by all coordinate
idempotents is not finitely generated. Thus finite generation cannot be dropped
from the ideal-detection condition for arbitrary localization products.

The finite product criterion also recovers faithful flatness of the canonical
localizations of `ZMod 6` away from three and four, starting from their jointly
faithfully flat direct sum. The unital-algebra criterion gives proper ideal
action on the countable product of two-by-two matrices over `ZMod 2`, without
requiring the algebra to be commutative.

## References

These examples use the models and canonical actions in `LocalizationProduct`
and `LocalizationProductInfinite`. They apply CoherentModules' product and
unital-algebra criteria. The ideal-membership contradiction uses Mathlib's
`Submonoid.mem_powers`, `Set.disjoint_left`, and
`Ideal.mem_span_range_self`.
-/

@[expose] public section

noncomputable section

namespace CoherentModulesTest.Flat.LocalizationProductCriteria

section Infinite

open LocalizationProductInfinite

-- The sequence ring also admits coordinatewise-scalar Pi instances. Use the
-- same stock common-R structures as the localization product model.
local instance : SMul R Product := Pi.instSMul
local instance : Module R Product := Pi.module ℕ A R
local instance : Algebra R Product := Pi.algebra ℕ A

/-- Every finitely generated proper ideal of `ℕ → ZMod 2` omits a coordinate
idempotent, as detected by the faithfully flat product of their localizations. -/
theorem exists_e_not_mem (I : Ideal R) (hI : I.FG) (hproper : I ≠ ⊤) :
    ∃ i : ℕ, e i ∉ I := by
  obtain ⟨i, hi⟩ :=
    ((Module.FaithfullyFlat.pi_localization_iff R
      (fun i ↦ Submonoid.powers (e i)) A).mp product_faithfullyFlat).2 I hI hproper
  exact ⟨i, fun hei ↦ Set.disjoint_left.mp hi (Submonoid.mem_powers (e i)) hei⟩

/-- The proper ideal spanned by the coordinate idempotents of `ℕ → ZMod 2`
is not finitely generated: it contains every coordinate idempotent. -/
theorem span_e_not_fg : ¬ (Ideal.span (Set.range e)).FG := by
  intro hfg
  obtain ⟨i, hi⟩ := exists_e_not_mem (Ideal.span (Set.range e)) hfg span_e_ne_top
  exact hi (Ideal.mem_span_range_self (f := e) (x := i))

end Infinite

section Finite

open LocalizationProduct

example : Module.FaithfullyFlat (ZMod 6) ZModSixProduct := by
  apply (Module.FaithfullyFlat.pi_away_iff (ZMod 6) zmodSixDenominator).mpr
  exact (Module.FaithfullyFlat.directSum_away_iff (ZMod 6) zmodSixDenominator).mp
    LocalizationZeroDivisors.zmodSixAwayThreeFourDirectSum.2.1

end Finite

section Matrices

open LocalizationProduct

/-- Finitely generated proper ideals of `ZMod 2` act with proper image on the
countable product of its noncommutative two-by-two matrix algebras. -/
theorem matrixSequence_ideal_smul_ne_top (I : Ideal (ZMod 2))
    (hI : I.FG) (hproper : I ≠ ⊤) :
    I • (⊤ : Submodule (ZMod 2) MatrixSequence) ≠ ⊤ := by
  exact ((Module.FaithfullyFlat.algebra_iff_flat_and_fg_proper_ideal
    (ZMod 2) MatrixSequence).mp matrixSequence_faithfullyFlat).2 I hI hproper

end Matrices

end CoherentModulesTest.Flat.LocalizationProductCriteria
