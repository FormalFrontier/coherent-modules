/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Formal Frontier AI agents
-/
module

public import CoherentModules.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Tensor products of coherent modules

This file proves that tensoring a coherent module with a finitely presented module preserves
coherence. The ring acting on the coherent left factor may be independent of the commutative
base ring: it only needs to act on that factor, commuting with the base action. The tensor
product has the standard left action induced from the given action on the left factor.

## Main declarations

* `Module.IsCoherent.tensorProduct_left`: if `M` is coherent over `S` and `N` is finitely
  presented over `R`, then `M ⊗[R] N` is coherent over `S` for its induced left action.
* `Module.IsCoherent.tensorProduct`: the tensor product of a finitely presented module and a
  coherent module over the same commutative ring is coherent.
-/

open scoped TensorProduct

@[expose] public section

universe u v w x

namespace Module.IsCoherent

variable {R : Type u} [CommRing R]

section IndependentScalars

variable {S : Type x} [Ring S]
variable {M : Type v} [AddCommMonoid M] [Module R M] [Module S M]
variable [SMulCommClass R S M]
variable {N : Type w} [AddCommMonoid N] [Module R N]

/-- Tensoring a coherent left module with a finitely presented module preserves coherence for
its induced left action. The scalar ring `S` need not be an algebra or even a module over `R`;
only the given actions on `M` must commute. -/
theorem tensorProduct_left [Module.IsCoherent S M] [Module.FinitePresentation R N] :
    Module.IsCoherent S (M ⊗[R] N) := by
  -- The induced groups retain the original additive monoids and module structures.
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R (M := M)
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup R (M := N)
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R N
  -- Use the usual coordinate equivalence, now viewed as S-linear by commutation.
  let tensorPiEquiv (k : ℕ) : M ⊗[R] (Fin k → R) ≃ₗ[S] (Fin k → M) :=
    (TensorProduct.piScalarRight R R M (Fin k)).toAddEquiv.toLinearEquiv (by
      intro s z
      change TensorProduct.piScalarRight R R M (Fin k) (s • z) =
        s • TensorProduct.piScalarRight R R M (Fin k) z
      induction z with
      | tmul a b =>
        ext i
        simpa only [TensorProduct.smul_tmul', TensorProduct.piScalarRight_apply,
          TensorProduct.piScalarRightHom_tmul, Pi.smul_apply] using smul_comm (b i) s a
      | add z z' hz hz' =>
        simp only [smul_add, map_add, hz, hz'])
  -- These are the same functions as the maps in the tensorized R-presentation.
  let fS : M ⊗[R] (Fin n → R) →ₗ[S] M ⊗[R] N :=
    { toFun := LinearMap.lTensor M f
      map_add' := (LinearMap.lTensor M f).map_add
      map_smul' := by
        intro s z
        induction z with
        | tmul a b => rfl
        | add z z' hz hz' => simp only [smul_add, map_add, hz, hz'] }
  let gS : M ⊗[R] (Fin m → R) →ₗ[S] M ⊗[R] (Fin n → R) :=
    { toFun := LinearMap.lTensor M g
      map_add' := (LinearMap.lTensor M g).map_add
      map_smul' := by
        intro s z
        induction z with
        | tmul a b => rfl
        | add z z' hz hz' => simp only [smul_add, map_add, hz, hz'] }
  let _ : Module.IsCoherent S (M ⊗[R] (Fin n → R)) :=
    Module.IsCoherent.of_equiv (tensorPiEquiv n).symm
  let _ : Module.Finite S (M ⊗[R] (Fin m → R)) :=
    Module.Finite.equiv (tensorPiEquiv m).symm
  have hExact : Function.Exact gS fS := lTensor_exact M hgf hf
  have hSurjective : Function.Surjective fS := LinearMap.lTensor_surjective M hf
  have hker : (LinearMap.ker fS).FG := by
    rw [hExact.linearMap_ker_eq]
    exact Submodule.fg_range gS
  let _ : Module.IsCoherent S ((M ⊗[R] (Fin n → R)) ⧸ LinearMap.ker fS) :=
    Module.IsCoherent.quotient _ hker
  exact Module.IsCoherent.of_equiv (fS.quotKerEquivOfSurjective hSurjective)

end IndependentScalars

variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The tensor product of a finitely presented module and a coherent module is coherent. -/
theorem tensorProduct [Module.FinitePresentation R M] [Module.IsCoherent R N] :
    Module.IsCoherent R (M ⊗[R] N) := by
  let _ : Module.IsCoherent R (N ⊗[R] M) := tensorProduct_left (S := R)
  exact Module.IsCoherent.of_equiv (TensorProduct.comm R N M)

end Module.IsCoherent
