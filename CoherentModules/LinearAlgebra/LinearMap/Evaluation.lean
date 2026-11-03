/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Evaluation on a finite generating family

Semilinear maps out of a finitely generated semimodule are determined by their values on a finite
spanning family. When the scalar actions on the codomain commute, evaluation on such a family is a
linear injection into a finite product of the codomain.

The evaluation map is assembled from `LinearMap.pi`, `LinearMap.flip`, and `LinearMap.id`; its
coordinate at `i` sends `f` to `f (v i)`.
-/

@[expose] public section

universe uR uR₂ uS uM uN

namespace LinearMap

/-- A finitely generated semimodule has a finite spanning family and a bundled injective linear
map given by evaluation of semilinear maps on that family. -/
theorem exists_fin_injective_eval
    {R : Type uR} {R₂ : Type uR₂} {S : Type uS} {M : Type uM} {N : Type uN}
    [Semiring R] [Semiring R₂] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R₂ N] [Module S N] (σ : R →+* R₂)
    [SMulCommClass R₂ S N] [Module.Finite R M] :
    ∃ (n : ℕ) (v : Fin n → M) (e : (M →ₛₗ[σ] N) →ₗ[S] (Fin n → N)),
      Submodule.span R (Set.range v) = ⊤ ∧
        (∀ f i, e f i = f (v i)) ∧ Function.Injective e := by
  obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  refine ⟨n, v, LinearMap.pi (fun i ↦
    (LinearMap.flip (LinearMap.id : (M →ₛₗ[σ] N) →ₗ[S] (M →ₛₗ[σ] N))) (v i)), hv, ?_, ?_⟩
  · intro f i
    simp only [LinearMap.pi_apply, LinearMap.flip_apply, LinearMap.id_apply]
  · intro f g h
    exact LinearMap.ext_on_range hv fun i ↦ by
      simpa only [LinearMap.pi_apply, LinearMap.flip_apply, LinearMap.id_apply] using congrFun h i

end LinearMap
