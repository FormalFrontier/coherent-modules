/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.Algebra.Module.Coprime
import Mathlib.Algebra.Ring.Prod

/-!
# Coprime rows over semirings

The product of natural-number semirings gives a nonring example with two nonunit
scalars carrying different coordinates. The regular-semimodule specialization
recovers the scalar divisibility criterion.
-/

section

/-- The two coordinate projections recover one parameter without subtraction. -/
example : ∃! k : ℕ × ℕ,
    ((1, 0) : ℕ × ℕ) • k = (2, 0) ∧ ((0, 1) : ℕ × ℕ) • k = (0, 3) := by
  apply IsCoprime.existsUnique_smul_eq_pair
  · exact ⟨1, 1, by decide⟩
  · decide

variable {S : Type*} [CommSemiring S] {a b c : S}

/-- On the regular semimodule, range cancellation recovers coprime divisibility. -/
example (h : IsCoprime a b) : a ∣ b * c ↔ a ∣ c := by
  simpa only [Set.mem_range, smul_eq_mul, dvd_def, eq_comm] using
    (h.smul_mem_range_smul_iff (M := S) c)

end
