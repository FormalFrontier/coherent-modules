/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.Matrix.Submodule
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Length

/-!
# Submodules of columns

The full matrix action on two-dimensional columns over `ZMod 2` has length one,
whereas the coefficientwise `ZMod 2` action on the same columns has length two.
Matrix units prove simplicity directly, without using a submodule correspondence.
Even natural-number columns give a nonzero proper matrix-stable submodule through
the coordinatewise membership API.
-/

@[expose] public section

open scoped Matrix.Module

example :
    (fun _ : Fin 2 ↦ 2) ∈ Submodule.matrixColumns (I := Fin 2)
        (Submodule.span ℕ ({2} : Set ℕ)) ∧
      (fun _ : Fin 2 ↦ 1) ∉ Submodule.matrixColumns (I := Fin 2)
        (Submodule.span ℕ ({2} : Set ℕ)) := by
  constructor
  · exact Submodule.mem_matrixColumns.mpr fun _ ↦ Submodule.mem_span_singleton_self 2
  · intro h
    have h1 := (Submodule.mem_matrixColumns.mp h) 0
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h1
    exact (show ¬ 2 ∣ (1 : ℕ) by decide) ⟨a, by
      simpa [smul_eq_mul, Nat.mul_comm] using ha.symm⟩

example :
    Module.length (Matrix (Fin 2) (Fin 2) (ZMod 2)) (Fin 2 → ZMod 2) = 1 ∧
      Module.length (ZMod 2) (Fin 2 → ZMod 2) = 2 := by
  let : IsSimpleModule (Matrix (Fin 2) (Fin 2) (ZMod 2)) (Fin 2 → ZMod 2) :=
    { eq_bot_or_eq_top := fun P => by
        by_cases hP : P = ⊥
        · exact Or.inl hP
        · right
          obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
          obtain ⟨j, hj⟩ := Function.ne_iff.mp hv0
          have hj0 : v j ≠ 0 := hj
          have hsingle (i : Fin 2) (a : ZMod 2) : Pi.single i a ∈ P := by
            simpa [Matrix.Module.single_smul_semiring, smul_eq_mul, mul_assoc, hj0] using
              P.smul_mem (Matrix.single i j (a * (v j)⁻¹)) hv
          apply top_unique
          intro w _
          simpa only [Finset.univ_sum_single] using
            P.sum_mem (fun i (_ : i ∈ Finset.univ) ↦ hsingle i (w i)) }
  refine ⟨Module.length_eq_one _ _, ?_⟩
  rw [Module.length_eq_finrank, Module.finrank_fintype_fun_eq_card]
  rfl
