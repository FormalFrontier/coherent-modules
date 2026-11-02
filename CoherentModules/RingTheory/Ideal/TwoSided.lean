/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import Mathlib.Algebra.Module.Submodule.Map

public import Mathlib.Order.CompleteSublattice
public import Mathlib.RingTheory.Ideal.Lattice

/-!
# The complete sublattice of two-sided ideals

`Ideal.twoSidedIdeals R` is the complete sublattice of `Ideal R` with carrier
`{I : Ideal R | I.IsTwoSided}`. Its elements inherit their order and complete lattice
operations from the lattice of left ideals. In particular, suprema are ideal-generated
joins, not set-theoretic unions.

The coercion lemmas and forgetful complete lattice homomorphism are those of
`CompleteSublattice`; equality is governed by subtype and ideal extensionality.

## Credits

This construction uses Mathlib's `Ideal.IsTwoSided` predicate, its two-sided intersection
closure, and the complete-sublattice formalization by Oliver Nash. The ideal lattice
formalization is due to Kenny Lau, Chris Hughes and Mario Carneiro. The supremum closure
uses Mathlib's right-multiplication linear maps and submodule preimages.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [Semiring R]

/-- An arbitrary supremum of two-sided ideals in a semiring is two-sided. -/
theorem isTwoSided_sSup (s : Set (Ideal R)) (hs : ∀ I ∈ s, I.IsTwoSided) :
    (sSup s).IsTwoSided := by
  refine ⟨?_⟩
  intro a b ha
  have hle : sSup s ≤ Submodule.comap (LinearMap.mulRight R b) (sSup s) := by
    refine sSup_le ?_
    intro I hI x hx
    exact le_sSup hI (@Ideal.mul_mem_right R x b _ I (hs I hI) hx)
  exact hle ha

/-- The complete sublattice of two-sided ideals of a semiring. -/
def twoSidedIdeals (R : Type u) [Semiring R] : CompleteSublattice (Ideal R) :=
  CompleteSublattice.mk' {I : Ideal R | I.IsTwoSided}
    (by
      intro s hs
      exact isTwoSided_sSup s hs)
    (by
      intro s hs
      change (sInf s).IsTwoSided
      rw [sInf_eq_iInf']
      let : ∀ I : s, (I : Ideal R).IsTwoSided := fun I ↦ hs I.2
      infer_instance)

/-- Membership in the complete sublattice of two-sided ideals. -/
@[simp] theorem mem_twoSidedIdeals (I : Ideal R) :
    I ∈ twoSidedIdeals R ↔ I.IsTwoSided := Iff.rfl

end Ideal
