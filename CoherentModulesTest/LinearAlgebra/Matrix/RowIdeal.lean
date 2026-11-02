/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.LinearAlgebra.Matrix.RowIdeal

/-!
# Boundary cases and a left ideal that is not two-sided

Over a field, rows with second coordinate zero give a proper nonzero left ideal
in the two-by-two matrix ring. Its idempotent matrix unit is not nilpotent,
and right multiplication can leave the ideal. These checks distinguish the row
construction from entrywise coefficient ideals and two-sided ideals.
-/

section SecondColumn

variable {K : Type*} [Field K]

example :
    let S : Submodule K (Fin 2 → K) := Submodule.pi {1} fun _ => ⊥
    let J := S.matrixRows
    let E : Matrix (Fin 2) (Fin 2) K := Matrix.single 0 0 1
    let F : Matrix (Fin 2) (Fin 2) K := Matrix.single 0 1 1
    E ∈ J ∧ F ∉ J ∧ J ≠ ⊥ ∧ J ≠ ⊤ ∧ E * F = F ∧ ¬IsNilpotent E := by
  intro S J E F
  have hmem (A : Matrix (Fin 2) (Fin 2) K) : A ∈ J ↔ ∀ i, A i 1 = 0 := by
    simp [J, S, Submodule.mem_matrixRows, Submodule.mem_pi]
  have hE : E ∈ J := by
    rw [hmem]
    intro i
    simp [E]
  have hF : F ∉ J := by
    rw [hmem]
    intro h
    simpa [F] using h 0
  have hE0 : E ≠ 0 := by
    intro h
    have := congrArg (fun A : Matrix (Fin 2) (Fin 2) K => A 0 0) h
    simp [E] at this
  have hsq : E * E = E := by
    simp [E, Matrix.single_mul_single_same]
  have hpow : ∀ n : ℕ, E ^ (n + 1) = E := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, hsq]
  refine ⟨hE, hF, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hE0 (by simpa [h] using hE)
  · intro h
    exact hF (by simp [h])
  · simp [E, F, Matrix.single_mul_single_same]
  · rintro ⟨n, hn⟩
    apply hE0
    rw [← hpow n, pow_succ, hn, zero_mul]

end SecondColumn

section Degenerate

variable {R : Type*} [Semiring R] {I : Type*} [Fintype I] [DecidableEq I]

-- With no row positions, every row vector is the unique zero vector.
example [IsEmpty I] (J : Ideal (Matrix I I R)) : J.rowSubmodule = ⊥ := by
  ext v
  have hv : v = 0 := Subsingleton.elim _ _
  simp [hv]

-- The zero semiring needs no nontriviality assumption in the correspondence.
example [Subsingleton R] (S : Submodule R (I → R)) : S.matrixRows = ⊤ := by
  ext A
  simp only [Submodule.mem_matrixRows, Submodule.mem_top, iff_true]
  intro i
  have hi : A i = 0 := Subsingleton.elim _ _
  simpa only [hi] using S.zero_mem

end Degenerate
