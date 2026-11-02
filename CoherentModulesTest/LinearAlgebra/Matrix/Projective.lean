/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.Matrix.Projective

/-!
# Projective cyclic columns

The natural-number column module of length two is a nonzero cyclic projective module
over the full matrix semiring. The cyclic generator is the first standard column.
-/

open scoped Matrix.Module

example : Module.Projective (Matrix (Fin 2) (Fin 2) ℕ) (Fin 2 → ℕ) ∧
    ∀ x : Fin 2 → ℕ, ∃ A : Matrix (Fin 2) (Fin 2) ℕ, A • Pi.single 0 1 = x := by
  constructor
  · exact Matrix.Module.projective_iff_of_nonempty.mpr inferInstance
  · intro x
    refine ⟨fun i j => if j = 0 then x i else 0, ?_⟩
    ext i
    exact (Matrix.Module.smul_apply_semiring
      (I := Fin 2) (R := ℕ) (M := ℕ) (hM := inferInstance)
      (fun a b : Fin 2 => if b = 0 then x a else 0)
      (Pi.single 0 1) i).trans (by simp)
