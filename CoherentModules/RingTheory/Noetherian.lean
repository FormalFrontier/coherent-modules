/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Noetherian ascent under scalar clearing

For a semilinear map, suppose each target element can be multiplied by a scalar
with a left inverse into the image. Comap then reflects submodule order, so the
ascending-chain criterion transfers Noetherianity from source to target. In
particular, clearing by target units suffices. Neither the scalar homomorphism
nor the semilinear map needs to be surjective.

For regular semiring modules, unit clearing also identifies each left ideal
with the extension of its contraction. Units need not be central or come from
the source. Function-surjective maps satisfy unit clearing with the unit `1`.

## References

The argument uses Mathlib's submodule comap and ascending-chain criterion, and
extends the ideal unit-clearing argument in this library to semimodules. The
left-inverse formulation retains only the scalar recovery needed in that argument.
-/

@[expose] public section

universe uR uS uM uN

variable {R : Type uR} {S : Type uS} [Semiring R] [Semiring S]

section Module

variable {M : Type uM} {N : Type uN} [AddCommMonoid M] [AddCommMonoid N]
  [Module R M] [Module S N] {φ : R →+* S}

/-- Comap reflects submodule order if every target element can be cleared into
the image by a scalar with a left inverse. The inverse is on the left because
these are left semimodules. -/
theorem Submodule.comap_le_comap_iff_of_left_inv_smul_mem_range (f : M →ₛₗ[φ] N)
    (hclear : ∀ n : N, ∃ m : M, ∃ a b : S, b * a = 1 ∧ f m = a • n)
    {p q : Submodule S N} : p.comap f ≤ q.comap f ↔ p ≤ q := by
  constructor
  · intro h n hn
    obtain ⟨m, a, b, hba, hm⟩ := hclear n
    have hmp : m ∈ p.comap f := by
      rw [Submodule.mem_comap, hm]
      exact p.smul_mem a hn
    have hmq : f m ∈ q := Submodule.mem_comap.mp (h hmp)
    have hrecover : b • f m = n := by
      rw [hm, ← mul_smul, hba, one_smul]
    rw [← hrecover]
    exact q.smul_mem b hmq
  · exact Submodule.comap_mono

/-- Noetherianity ascends along a semilinear map if every target element can be
cleared into its image by a scalar with a left inverse. No surjectivity of the
scalar homomorphism is required. -/
theorem isNoetherian_of_left_inv_smul_mem_range (f : M →ₛₗ[φ] N)
    [IsNoetherian R M]
    (hclear : ∀ n : N, ∃ m : M, ∃ a b : S, b * a = 1 ∧ f m = a • n) :
    IsNoetherian S N := by
  apply monotone_stabilizes_iff_noetherian.mp
  intro c
  let d : ℕ →o Submodule R M :=
    ⟨fun i => (c i).comap f, fun _ _ hij => Submodule.comap_mono (c.monotone hij)⟩
  obtain ⟨i, hi⟩ :=
    (monotone_stabilizes_iff_noetherian.mpr (inferInstance : IsNoetherian R M)) d
  refine ⟨i, fun j hij => ?_⟩
  apply le_antisymm
  · exact (Submodule.comap_le_comap_iff_of_left_inv_smul_mem_range f hclear).mp
      (le_of_eq (hi j hij))
  · exact (Submodule.comap_le_comap_iff_of_left_inv_smul_mem_range f hclear).mp
      (le_of_eq (hi j hij).symm)

/-- Noetherianity ascends along a semilinear map when each target element can be
cleared into the image by a target unit. The units may depend on the element
and need not come from the source. -/
theorem isNoetherian_of_unit_smul_mem_range (f : M →ₛₗ[φ] N) [IsNoetherian R M]
    (hunit : ∀ n : N, ∃ m : M, ∃ u : Sˣ, f m = (u : S) • n) :
    IsNoetherian S N := by
  apply isNoetherian_of_left_inv_smul_mem_range f
  intro n
  obtain ⟨m, u, hm⟩ := hunit n
  exact ⟨m, (u : S), (↑(u⁻¹) : S), u.inv_mul, hm⟩

/-- Noetherianity ascends along a function-surjective semilinear map, without
requiring surjectivity of its scalar homomorphism. This generalizes Mathlib's
`isNoetherian_of_surjective`, whose range formulation uses that extra class. -/
theorem isNoetherian_of_surjective_semilinear (f : M →ₛₗ[φ] N)
    (hf : Function.Surjective f) [IsNoetherian R M] : IsNoetherian S N := by
  apply isNoetherian_of_unit_smul_mem_range f
  intro n
  obtain ⟨m, hm⟩ := hf n
  exact ⟨m, 1, by simpa only [Units.val_one, one_smul] using hm⟩

/-- When the scalar homomorphism is surjective, left-invertible scalar clearing
is equivalent to surjectivity of the semilinear map. This identifies the clearing
criterion with the range hypothesis in Mathlib's `isNoetherian_of_surjective`. -/
theorem LinearMap.range_eq_top_iff_left_inv_smul_mem_range [RingHomSurjective φ]
    (f : M →ₛₗ[φ] N) :
    LinearMap.range f = ⊤ ↔
      ∀ n : N, ∃ m : M, ∃ a b : S, b * a = 1 ∧ f m = a • n := by
  rw [LinearMap.range_eq_top]
  constructor
  · intro hf n
    obtain ⟨m, hm⟩ := hf n
    exact ⟨m, 1, 1, one_mul 1, by simpa only [one_smul] using hm⟩
  · intro hclear n
    obtain ⟨m, a, b, hba, hm⟩ := hclear n
    obtain ⟨r, hr⟩ := RingHomSurjective.is_surjective (σ := φ) b
    refine ⟨r • m, ?_⟩
    rw [f.map_smulₛₗ, hr, hm, ← mul_smul, hba, one_smul]

end Module

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
  apply isNoetherianRing_iff.mpr
  apply isNoetherian_of_unit_smul_mem_range f.toSemilinearMap
  intro s
  obtain ⟨u, r, hr⟩ := h s
  exact ⟨r, u, hr⟩
