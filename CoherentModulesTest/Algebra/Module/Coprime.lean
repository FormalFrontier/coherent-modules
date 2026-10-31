/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.Algebra.Module.Coprime
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Fin.VecNotation

/-!
# Unit-ideal scalar families over semirings

Products of natural-number semirings give nonring examples with nonunit scalars
carrying different coordinates. The regular-semimodule specialization recovers the
scalar divisibility criterion, and a three-coordinate family exercises gluing beyond
a selected pair.
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

/-- Three coordinate idempotents glue compatible data over a semiring without subtraction.
Each selected pair omits a coordinate, whereas the whole family generates one. -/
example :
    let a : Fin 3 → ℕ × ℕ × ℕ := ![(1, 0, 0), (0, 1, 0), (0, 0, 1)]
    let x : Fin 3 → ℕ × ℕ × ℕ := ![(2, 0, 0), (0, 3, 0), (0, 0, 5)]
    ∃! k : ℕ × ℕ × ℕ, ∀ i, a i • k = x i := by
  intro a x
  apply Ideal.existsUnique_smul_eq_of_span_range_eq_top a
  · let I := Ideal.span (Set.range a)
    have hmem (i : Fin 3) : a i ∈ I := Ideal.subset_span ⟨i, rfl⟩
    rw [Ideal.eq_top_iff_one]
    exact I.add_mem (I.add_mem (hmem 0) (hmem 1)) (hmem 2)
  · decide
