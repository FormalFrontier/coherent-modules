/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.Matrix.ColumnHom

/-!
# Boundary cases for the column Hom and End equivalences

Coordinate extension preserves right multiplication on a non-ring regular module,
and the End equivalence keeps the opposite-semiring orientation over arbitrary
possibly noncommutative coefficients. Empty columns cannot recover a coefficient map.
-/

open scoped Matrix.Module

-- The Hom equivalence applies to semimodules without additive inverses.
example (v : Fin 2 → ℕ) (i : Fin 2) :
    LinearMap.matrixModuleHomAddEquiv (Fin 2) (LinearMap.mulRight ℕ 2) v i = v i * 2 := rfl

-- Regular endomorphisms are right multiplications, even for noncommutative coefficients.
example {R : Type*} [Semiring R] (r : Rᵐᵒᵖ) (v : Fin 2 → R) (i : Fin 2) :
    ((RingEquiv.moduleEndSelf R).trans (Module.matrixModuleEndRingEquiv (Fin 2))) r v i =
      v i * r.unop := rfl

-- For empty columns, the surjective extension is not generally injective.
example : ¬ Function.Injective (LinearMap.matrixModuleMap (Fin 0) (R := ℕ) (M := ℕ) (N := ℕ)) := by
  intro h
  have heq : (0 : ℕ →ₗ[ℕ] ℕ) = LinearMap.id := h (Subsingleton.elim _ _)
  have hone := LinearMap.congr_fun heq 1
  simp at hone
