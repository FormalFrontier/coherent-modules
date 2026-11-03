/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.FinitePresentation
public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Coherent trivial square-zero extensions

A trivial square-zero extension of a left coherent ring by a bimodule that is finitely
presented on the left is left coherent. The compatible right action need not be central.

The proof combines coherence of products with scalar restriction. Its regular-action tower
argument is also used in `CoherentModules.Algebra.TrivSqZeroExt.Noetherian`.
-/

@[expose] public section

universe uR uM

namespace TrivSqZeroExt

/-- A trivial square-zero extension by a bimodule finitely presented on the left is
left coherent. -/
theorem isCoherentRing
    {R : Type uR} {M : Type uM}
    [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M]
    [IsCoherentRing R] [Module.FinitePresentation R M] :
    IsCoherentRing (TrivSqZeroExt R M) := by
  let S := TrivSqZeroExt R M
  have : Module.IsCoherent R M := Module.FinitePresentation.isCoherent
  have : Module.IsCoherent R S := inferInstanceAs (Module.IsCoherent R (R × M))
  have : Module.Finite R S := inferInstance
  have : IsScalarTower R S S :=
    ⟨fun r x y => by
      change (r • x) * y = r • (x * y)
      rw [← inl_mul_eq_smul, ← inl_mul_eq_smul, mul_assoc]⟩
  exact ⟨Module.IsCoherent.of_restrictScalars R⟩

end TrivSqZeroExt
