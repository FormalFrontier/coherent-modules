/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.LinearAlgebra.Matrix.ReconstructionCoherence

/-!
A nonzero natural-number coefficient survives additive restriction and the change from
coordinate zero to coordinate one. This exercises the semiring API outside the ring case.
-/

open Matrix.Module
open scoped Matrix.Module

example :
    coefficientEquiv ℕ (Fin 2) ℕ 1
      (coordinateChange ℕ (Fin 2) (Fin 2 → ℕ) 0 1
        (coordinateMap ℕ (Fin 2) 0
          ((LinearMap.id : (Fin 2 → ℕ) →ₗ[Matrix (Fin 2) (Fin 2) ℕ] (Fin 2 → ℕ)) +
            LinearMap.id)
          ((coefficientEquiv ℕ (Fin 2) ℕ 0).symm 1))) = 2 := by
  let x := coordinateMap ℕ (Fin 2) 0
    ((LinearMap.id : (Fin 2 → ℕ) →ₗ[Matrix (Fin 2) (Fin 2) ℕ] (Fin 2 → ℕ)) +
      LinearMap.id) ((coefficientEquiv ℕ (Fin 2) ℕ 0).symm 1)
  change coefficientEquiv ℕ (Fin 2) ℕ 1
    (coordinateChange ℕ (Fin 2) (Fin 2 → ℕ) 0 1 x) = 2
  calc
    _ = coefficientEquiv ℕ (Fin 2) ℕ 0 x :=
      DFunLike.congr_fun (coefficientEquiv_coordinateChange ℕ (Fin 2) ℕ 0 1) x
    _ = 2 := by
      dsimp [x]
      rw [map_add]
      simp
