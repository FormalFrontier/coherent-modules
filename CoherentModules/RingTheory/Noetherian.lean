/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Left Noetherianity under unit clearing

Suppose every element of a target semiring can be multiplied on the left by a
unit into the image of a semiring homomorphism. Every left ideal of the target
is then the extension of its contraction. Consequently left Noetherianity
passes from the source to the target.

The units need not be central or come from the source. Surjective homomorphisms
satisfy the hypothesis by using the unit `1`.
-/

@[expose] public section

universe u v

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S]

/-- Surjectivity implies that each target element can be cleared into the image
by left multiplication by a unit. -/
theorem RingHom.exists_unit_mul_mem_range_of_surjective (f : R →+* S)
    (hf : Function.Surjective f) (s : S) :
    ∃ u : Sˣ, (u : S) * s ∈ Set.range f := by
  refine ⟨1, ?_⟩
  simpa using hf s

/-- If every target element can be multiplied on the left by a unit into the
image, extension of the contraction recovers every left ideal. -/
theorem Ideal.map_comap_eq_of_unit_mul_mem_range (f : R →+* S)
    (h : ∀ s : S, ∃ u : Sˣ, (u : S) * s ∈ Set.range f) (I : Ideal S) :
    (I.comap f).map f = I := by
  apply le_antisymm Ideal.map_comap_le
  intro x hx
  obtain ⟨u, y, hy⟩ := h x
  have hyI : y ∈ I.comap f := by
    apply Ideal.mem_comap.mpr
    rw [hy]
    exact I.mul_mem_left _ hx
  apply (Ideal.unit_mul_mem_iff_mem _ u.isUnit).mp
  rw [← hy]
  exact Ideal.mem_map_of_mem f hyI

/-- Left Noetherianity passes along a semiring homomorphism when every target
element can be multiplied on the left by a unit into its image. -/
theorem isNoetherianRing_of_unit_mul_mem_range (f : R →+* S)
    (h : ∀ s : S, ∃ u : Sˣ, (u : S) * s ∈ Set.range f) [IsNoetherianRing R] :
    IsNoetherianRing S := by
  apply (isNoetherianRing_iff_ideal_fg S).mpr
  intro I
  rw [← Ideal.map_comap_eq_of_unit_mul_mem_range f h I]
  exact (Ideal.fg_of_isNoetherianRing (I.comap f)).map f
