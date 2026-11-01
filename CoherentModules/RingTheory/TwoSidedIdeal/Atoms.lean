/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Order.ZornAtoms
public import Mathlib.RingTheory.TwoSidedIdeal.Lattice

/-!
# Coatomicity of two-sided ideals

A nonempty directed supremum of two-sided ideals is their union. In a unital ring,
this implies that a chain of proper two-sided ideals has a proper upper bound:
its union cannot contain `1`. Zorn's lemma then gives coatomicity, without
assuming associativity or nontriviality of the ring.

## References

The proof uses Mathlib's two-sided ideal API by Jujian Zhang and its
order-theoretic Zorn API by Yury Kudryashov.
-/

@[expose] public section

namespace TwoSidedIdeal

/-- Membership in the supremum of a nonempty directed set of two-sided ideals
is membership in one of the ideals. -/
lemma mem_sSup_of_directedOn {R : Type*} [NonUnitalNonAssocRing R]
    {s : Set (TwoSidedIdeal R)} (hs : s.Nonempty) (hd : DirectedOn (· ≤ ·) s) {x : R} :
    x ∈ sSup s ↔ ∃ I ∈ s, x ∈ I := by
  let J : TwoSidedIdeal R := .mk' {y | ∃ I ∈ s, y ∈ I}
    (by obtain ⟨I, hI⟩ := hs; exact ⟨I, hI, I.zero_mem⟩)
    (by
      rintro y z ⟨I, hI, hy⟩ ⟨K, hK, hz⟩
      obtain ⟨L, hL, hIL, hKL⟩ := hd I hI K hK
      exact ⟨L, hL, L.add_mem (hIL hy) (hKL hz)⟩)
    (by rintro y ⟨I, hI, hy⟩; exact ⟨I, hI, I.neg_mem hy⟩)
    (by rintro y z ⟨I, hI, hz⟩; exact ⟨I, hI, I.mul_mem_left y z hz⟩)
    (by rintro y z ⟨I, hI, hy⟩; exact ⟨I, hI, I.mul_mem_right y z hy⟩)
  have hJ (y : R) : y ∈ J ↔ ∃ I ∈ s, y ∈ I := mem_mk' _ _ _ _ _ _ y
  constructor
  · intro hx
    have hle : sSup s ≤ J := sSup_le fun I hI y hy => (hJ y).mpr ⟨I, hI, hy⟩
    exact (hJ x).mp (hle hx)
  · rintro ⟨I, hI, hx⟩
    exact (le_sSup hI) hx

/-- The two-sided ideals of a unital, possibly nonassociative ring form a coatomic lattice.
Thus every proper two-sided ideal is contained in a maximal proper two-sided ideal. -/
theorem isCoatomic (R : Type*) [NonAssocRing R] : IsCoatomic (TwoSidedIdeal R) := by
  apply IsCoatomic.of_isChain_bounded
  intro s hs hne htop
  refine ⟨sSup s, ?_, fun I hI => le_sSup hI⟩
  intro h
  have h1 : (1 : R) ∈ sSup s := by rw [h]; exact mem_top R
  obtain ⟨I, hI, hI1⟩ := (mem_sSup_of_directedOn hne hs.directedOn).mp h1
  exact htop ((I.one_mem_iff.mp hI1) ▸ hI)

end TwoSidedIdeal
