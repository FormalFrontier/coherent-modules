/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Formalization Worker A
-/
module

public import CoherentModules.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensor products of coherent modules

This file proves that tensoring a coherent module with a finitely presented module preserves
coherence.

## Main declaration

* `Module.IsCoherent.tensorProduct`: the tensor product of a finitely presented module and a
  coherent module is coherent.
-/

open scoped TensorProduct

@[expose] public section

universe u v w

namespace Module.IsCoherent

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The tensor product of a finitely presented module and a coherent module is coherent. -/
theorem tensorProduct [Module.FinitePresentation R M] [Module.IsCoherent R N] :
    Module.IsCoherent R (M ⊗[R] N) := by
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  let tensorPiEquiv (k : ℕ) : (Fin k → R) ⊗[R] N ≃ₗ[R] (Fin k → N) :=
    (TensorProduct.comm R (Fin k → R) N).trans
      (TensorProduct.piScalarRight R R N (Fin k))
  let _ : Module.IsCoherent R (Fin n → N) := inferInstance
  let _ : Module.IsCoherent R ((Fin n → R) ⊗[R] N) :=
    Module.IsCoherent.of_equiv (tensorPiEquiv n).symm
  let _ : Module.IsCoherent R (Fin m → N) := inferInstance
  let _ : Module.IsCoherent R ((Fin m → R) ⊗[R] N) :=
    Module.IsCoherent.of_equiv (tensorPiEquiv m).symm
  let _ : Module.IsCoherent R
      (((Fin n → R) ⊗[R] N) ⧸ LinearMap.range (LinearMap.rTensor N g)) :=
    Module.IsCoherent.cokernel (LinearMap.rTensor N g)
  exact Module.IsCoherent.of_equiv (rTensor.equiv N hgf hf)

end Module.IsCoherent
