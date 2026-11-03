/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.End.StableKernelRange
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Stable kernel and range examples

Doubling on `ZMod 8 × ZMod 3`, with the stock natural-number action, has two
nonzero stable summands at bound three. The nilpotent restriction has nonzero
square. The offset-indexed kernel stability conclusion also agrees with the
stock division-ring theorem.
-/

@[expose] public section

namespace StableKernelRangeExamples

/-- Doubling with its given natural-number linear structure. -/
def doubleResidues : Module.End ℕ (ZMod 8 × ZMod 3) where
  toFun x := (2 * x.1, 2 * x.2)
  map_add' := by
    intro x y
    apply Prod.ext <;> simp [mul_add]
  map_smul' := by
    intro c x
    apply Prod.ext <;> simp [mul_left_comm]

/-- The stable splitting has a nilpotent block of exact index three. -/
theorem doubleResidues_stable_split :
    LinearMap.ker (doubleResidues ^ 3) = LinearMap.ker (doubleResidues ^ (3 + 1)) ∧
      LinearMap.range (doubleResidues ^ 3) = LinearMap.range (doubleResidues ^ (3 + 1)) ∧
      LinearMap.ker (doubleResidues ^ 3) =
        (⊤ : Submodule ℕ (ZMod 8)).prod (⊥ : Submodule ℕ (ZMod 3)) ∧
      LinearMap.range (doubleResidues ^ 3) =
        (⊥ : Submodule ℕ (ZMod 8)).prod (⊤ : Submodule ℕ (ZMod 3)) ∧
      Module.End.kerPowRestrict doubleResidues 3 ^ 2 ≠ 0 := by
  have hpow3 (x : ZMod 8 × ZMod 3) :
      (doubleResidues ^ 3) x = (0, 2 * x.2) := by
    change (2 * (2 * (2 * x.1)), 2 * (2 * (2 * x.2))) = (0, 2 * x.2)
    have h8 : (2 : ZMod 8) * 2 * 2 = 0 := by decide
    have h3 : (2 : ZMod 3) * 2 * 2 = 2 := by decide
    apply Prod.ext <;> simp only [← mul_assoc, h8, h3, zero_mul]
  have hpow4 (x : ZMod 8 × ZMod 3) :
      (doubleResidues ^ (3 + 1)) x = (0, x.2) := by
    change (2 * (2 * (2 * (2 * x.1))), 2 * (2 * (2 * (2 * x.2)))) = (0, x.2)
    have h8 : (2 : ZMod 8) * 2 * 2 * 2 = 0 := by decide
    have h3 : (2 : ZMod 3) * 2 * 2 * 2 = 1 := by decide
    apply Prod.ext <;> simp only [← mul_assoc, h8, h3, zero_mul, one_mul]
  have htwo (z : ZMod 3) : 2 * (2 * z) = z := by
    have h3 : (2 : ZMod 3) * 2 = 1 := by decide
    simp only [← mul_assoc, h3, one_mul]
  have htwozero (z : ZMod 3) : 2 * z = 0 ↔ z = 0 := by
    constructor
    · intro hz
      calc
        z = 2 * (2 * z) := (htwo z).symm
        _ = 0 := by rw [hz, mul_zero]
    · rintro rfl
      exact mul_zero _
  have hker3 : LinearMap.ker (doubleResidues ^ 3) =
      (⊤ : Submodule ℕ (ZMod 8)).prod (⊥ : Submodule ℕ (ZMod 3)) := by
    ext x
    change ((doubleResidues ^ 3) x = (0, 0)) ↔
      (x.1 ∈ (⊤ : Submodule ℕ (ZMod 8)) ∧ x.2 ∈ (⊥ : Submodule ℕ (ZMod 3)))
    rw [hpow3]
    simp [htwozero]
  have hker4 : LinearMap.ker (doubleResidues ^ (3 + 1)) =
      (⊤ : Submodule ℕ (ZMod 8)).prod (⊥ : Submodule ℕ (ZMod 3)) := by
    ext x
    change ((doubleResidues ^ (3 + 1)) x = (0, 0)) ↔
      (x.1 ∈ (⊤ : Submodule ℕ (ZMod 8)) ∧ x.2 ∈ (⊥ : Submodule ℕ (ZMod 3)))
    rw [hpow4]
    simp
  have hrange3 : LinearMap.range (doubleResidues ^ 3) =
      (⊥ : Submodule ℕ (ZMod 8)).prod (⊤ : Submodule ℕ (ZMod 3)) := by
    ext x
    change (∃ y, (doubleResidues ^ 3) y = x) ↔
      (x.1 ∈ (⊥ : Submodule ℕ (ZMod 8)) ∧ x.2 ∈ (⊤ : Submodule ℕ (ZMod 3)))
    simp only [Submodule.mem_bot, Submodule.mem_top, and_true]
    constructor
    · rintro ⟨y, hy⟩
      simpa only [hpow3, Prod.fst] using (congrArg Prod.fst hy).symm
    · intro hx
      refine ⟨(0, 2 * x.2), ?_⟩
      rw [hpow3]
      exact Prod.ext hx.symm (htwo x.2)
  have hrange4 : LinearMap.range (doubleResidues ^ (3 + 1)) =
      (⊥ : Submodule ℕ (ZMod 8)).prod (⊤ : Submodule ℕ (ZMod 3)) := by
    ext x
    change (∃ y, (doubleResidues ^ (3 + 1)) y = x) ↔
      (x.1 ∈ (⊥ : Submodule ℕ (ZMod 8)) ∧ x.2 ∈ (⊤ : Submodule ℕ (ZMod 3)))
    simp only [Submodule.mem_bot, Submodule.mem_top, and_true]
    constructor
    · rintro ⟨y, hy⟩
      simpa only [hpow4, Prod.fst] using (congrArg Prod.fst hy).symm
    · intro hx
      refine ⟨(0, x.2), ?_⟩
      rw [hpow4]
      exact Prod.ext hx.symm rfl
  refine ⟨hker3.trans hker4.symm, hrange3.trans hrange4.symm, hker3, hrange3, ?_⟩
  let x : LinearMap.ker (doubleResidues ^ 3) :=
    ⟨(1, 0), by rw [hker3]; simp⟩
  intro hzero
  have h := congrArg
    (fun g : Module.End ℕ (LinearMap.ker (doubleResidues ^ 3)) =>
      ((g x : LinearMap.ker (doubleResidues ^ 3)) : ZMod 8 × ZMod 3).1) hzero
  change (2 * (2 * (1 : ZMod 8))) = 0 at h
  exact (by decide : (2 * (2 * (1 : ZMod 8))) ≠ 0) h

end StableKernelRangeExamples

section DivisionRing

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

/- The semiring theorem specializes to the original division-ring kernel theorem. -/
example {f : Module.End K V} {n : ℕ}
    (h : LinearMap.ker (f ^ n) = LinearMap.ker (f ^ (n + 1))) :
    Module.End.ker_pow_constant_of_semiring f n h = Module.End.ker_pow_constant h :=
  Subsingleton.elim _ _

end DivisionRing
