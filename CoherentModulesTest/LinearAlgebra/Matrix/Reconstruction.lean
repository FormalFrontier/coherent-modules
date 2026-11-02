/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.LinearAlgebra.Matrix.Reconstruction
import Mathlib.Data.ZMod.Basic

open Matrix.Module
open scoped Matrix.Module

private theorem regularMatrixModule {R I : Type*} [Semiring R] [Fintype I] [DecidableEq I] :
    @matrixModuleSemiring I R (I → R) _ _ _ _
      (@Pi.module I (fun _ => R) R _ (fun _ => inferInstance)
        (fun _ => @Semiring.toModule R _)) =
      @Semiring.toModule (Matrix I I R) _ := by
  apply Module.ext'
  intro A B
  funext i j
  simp only [smul_apply_semiring, Finset.sum_apply]
  rfl

-- A genuinely nongroup coefficient module, with a nonzero supported vector.
example :
    let x : coordinateSubmodule ℕ (Fin 2) (Fin 2 → ℕ) 0 :=
      ⟨Pi.single 0 1, single_mem_coordinateSubmodule ℕ (Fin 2) ℕ 0 1⟩
    coefficientEquiv ℕ (Fin 2) ℕ 0 x = 1 ∧ x ≠ 0 := by
  constructor
  · simp
  · intro h
    have h0 := congrArg
      (fun x : coordinateSubmodule ℕ (Fin 2) (Fin 2 → ℕ) 0 => (x : Fin 2 → ℕ) 0) h
    simp at h0

-- Reconstruction assembles the supported coefficient vectors, without additive inverses.
example (v : Fin 2 → ℕ) :
    coordinateReconstruction ℕ (Fin 2) (Fin 2 → ℕ) 0
      (fun i => (coefficientEquiv ℕ (Fin 2) ℕ 0).symm (v i)) = v := by
  funext j
  simp [coordinateReconstruction_apply, Matrix.Module.single_smul_semiring,
    Finset.sum_apply]

-- The regular module over matrices with noncommutative coefficients recovers a row,
-- not one coefficient. Both coefficient self-action and the given regular matrix action
-- are specified, independently of the scoped column instance.
example :
    let R := Matrix (Fin 2) (Fin 2) (ZMod 2)
    let S := Matrix (Fin 2) (Fin 2) R
    let hPRR : Module R (Fin 2 → R) :=
      @Pi.module (Fin 2) (fun _ => R) R _ (fun _ => inferInstance)
        (fun _ => @Semiring.toModule R _)
    letI : Module R (Fin 2 → R) := hPRR
    Nonempty ((@coordinateSubmodule R (Fin 2) S _ _ _ _
      (@Semiring.toModule S _) 0) ≃ₗ[R] (Fin 2 → R)) := by
  let R := Matrix (Fin 2) (Fin 2) (ZMod 2)
  let S := Matrix (Fin 2) (Fin 2) R
  let hPRR : Module R (Fin 2 → R) :=
    @Pi.module (Fin 2) (fun _ => R) R _ (fun _ => inferInstance)
      (fun _ => @Semiring.toModule R _)
  let : Module R (Fin 2 → R) := hPRR
  let hCM : Module S S := @matrixModuleSemiring (Fin 2) R (Fin 2 → R) _ _ _ _ hPRR
  have hm : hCM = @Semiring.toModule S _ := regularMatrixModule
  have result : Nonempty ((@coordinateSubmodule R (Fin 2) S _ _ _ _
      (@Semiring.toModule S _) 0) ≃ₗ[R] (Fin 2 → R)) := by
    rw [← hm]
    exact ⟨@coefficientEquiv R (Fin 2) (Fin 2 → R) _ _ _ _ hPRR 0⟩
  exact result

-- No index is selected when the matrix index type is empty.
example (N : Type*) [AddCommMonoid N] [Module (Matrix Empty Empty ℕ) N] :
    Subsingleton N :=
  Module.subsingleton (Matrix Empty Empty ℕ) N
