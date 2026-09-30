/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Formal Frontier AI agents
-/
module

public import CoherentModules.Basic

/-!
# Linear maps into coherent modules

This file proves that the module of linear maps from a finitely presented module into a coherent
module is coherent.

## Main declaration

* `Module.IsCoherent.linearMap`: coherence of a linear-map module whose source is finitely
  presented and whose target is coherent.
-/

@[expose] public section

universe u v w

namespace Module.IsCoherent

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Linear maps from a finitely presented module into a coherent module form a coherent module. -/
theorem linearMap [Module.FinitePresentation R M] [Module.IsCoherent R N] :
    Module.IsCoherent R (M →ₗ[R] N) := by
  obtain ⟨n, m, f, g, hf, hgf⟩ := Module.FinitePresentation.exists_fin' R M
  let _ : Module.IsCoherent R ((Fin n → R) →ₗ[R] N) :=
    Module.IsCoherent.of_equiv (LinearEquiv.piRing R N (Fin n) R).symm
  let _ : Module.IsCoherent R ((Fin m → R) →ₗ[R] N) :=
    Module.IsCoherent.of_equiv (LinearEquiv.piRing R N (Fin m) R).symm
  let precompF := LinearMap.lcomp R N f
  let precompG := LinearMap.lcomp R N g
  have hprecomp : Function.Exact precompF precompG :=
    LinearMap.exact_lcomp_of_exact_of_surjective N hgf hf
  let _ : Module.IsCoherent R (LinearMap.ker precompG) := Module.IsCoherent.ker precompG
  let e : (M →ₗ[R] N) ≃ₗ[R] LinearMap.ker precompG :=
    (LinearEquiv.ofInjective precompF (LinearMap.lcomp_injective_of_surjective f hf)).trans
      (LinearEquiv.ofEq _ _ hprecomp.linearMap_ker_eq.symm)
  exact Module.IsCoherent.of_equiv e.symm

end Module.IsCoherent
