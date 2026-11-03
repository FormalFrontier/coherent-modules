/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.LinearMap.Evaluation
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.RingTheory.Artinian.Module

/-!
# Artinian modules of semilinear maps

Semilinear maps from a finitely generated semimodule to an Artinian module form an Artinian module
under a commuting external ring action on the codomain. Evaluation on a finite spanning family
embeds this space into a finite product of the codomain.
-/

@[expose] public section

universe uR uR₂ uS uM uN

/-- Semilinear maps out of a finitely generated semimodule form an Artinian module under an
external ring action on the codomain, provided that action commutes with the codomain's scalar
action and makes the codomain Artinian. -/
theorem isArtinian_semilinearMap
    {R : Type uR} {R₂ : Type uR₂} {S : Type uS} {M : Type uM} {N : Type uN}
    [Semiring R] [Semiring R₂] [Ring S] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R₂ N] [Module S N] (σ : R →+* R₂)
    [SMulCommClass R₂ S N] [Module.Finite R M] [IsArtinian S N] :
    IsArtinian S (M →ₛₗ[σ] N) := by
  let := Module.addCommMonoidToAddCommGroup S (M := N)
  obtain ⟨n, _v, e, _hspan, _happly, hinj⟩ :=
    LinearMap.exists_fin_injective_eval (S := S) (M := M) (N := N) σ
  have : IsArtinian S (Fin n → N) := inferInstance
  exact isArtinian_of_injective e hinj
