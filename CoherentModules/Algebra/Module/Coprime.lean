/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Basic
public import Mathlib.RingTheory.Coprime.Basic

/-!
# Coprime scalar rows in semimodules

A Bézout identity for two scalars recovers a unique common parameter from a compatible
pair in any semimodule. Neither subtraction nor additive cancellation is needed.
Here `IsCoprime a b` means that `r * a + s * b = 1` for some scalars `r, s`, not merely
that `a` and `b` have no common nonunit divisor.

The range-membership criterion specializes to Mathlib's coprime divisibility
criterion on the regular semimodule.

## References

This uses Mathlib's Bézout definition of `IsCoprime` and its scalar divisibility API
in `Mathlib.RingTheory.Coprime.Basic`.
-/

@[expose] public section

universe u v

namespace IsCoprime

variable {S : Type u} [CommSemiring S]
variable {M : Type v} [AddCommMonoid M] [Module S M]
variable {a b : S}

/-- A compatible pair has a unique common parameter when the two scalars satisfy
Bézout's identity. This holds for semimodules without additive inverses or cancellation. -/
theorem existsUnique_smul_eq_pair (h : IsCoprime a b) {x y : M}
    (hxy : b • x = a • y) : ∃! k : M, a • k = x ∧ b • k = y := by
  obtain ⟨r, s, hrs⟩ := h
  let k := r • x + s • y
  have hak : a • k = x := by
    calc
      a • k = r • (a • x) + s • (a • y) := by
        dsimp only [k]
        rw [smul_add, smul_comm a r x, smul_comm a s y]
      _ = r • (a • x) + s • (b • x) := by rw [hxy]
      _ = (r * a + s * b) • x := by rw [add_smul, mul_smul, mul_smul]
      _ = x := by rw [hrs, one_smul]
  have hbk : b • k = y := by
    calc
      b • k = r • (b • x) + s • (b • y) := by
        dsimp only [k]
        rw [smul_add, smul_comm b r x, smul_comm b s y]
      _ = r • (a • y) + s • (b • y) := by rw [hxy]
      _ = (r * a + s * b) • y := by rw [add_smul, mul_smul, mul_smul]
      _ = y := by rw [hrs, one_smul]
  refine ⟨k, ⟨hak, hbk⟩, ?_⟩
  rintro z ⟨haz, hbz⟩
  calc
    z = (r * a + s * b) • z := by rw [hrs, one_smul]
    _ = r • (a • z) + s • (b • z) := by rw [add_smul, mul_smul, mul_smul]
    _ = r • x + s • y := by rw [haz, hbz]
    _ = k := rfl

/-- Multiplication by a coprime scalar reflects membership in the range of a scalar
multiplication map. On the regular semimodule this is coprime divisibility cancellation. -/
theorem smul_mem_range_smul_iff (h : IsCoprime a b) (x : M) :
    b • x ∈ Set.range (fun y : M ↦ a • y) ↔ x ∈ Set.range (fun y : M ↦ a • y) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨k, hk, _⟩ := h.existsUnique_smul_eq_pair hy.symm
    exact ⟨k, hk.1⟩
  · rintro ⟨y, rfl⟩
    exact ⟨b • y, smul_comm a b y⟩

end IsCoprime
