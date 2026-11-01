/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Finite-submodule adic cofinality

`Ideal.HasFiniteSubmoduleAdicCofinality` says that the intrinsic ideal-power
filtration of every finitely generated submodule of a finite module is cofinal
with the filtration induced from the ambient module. Neither the ideal nor the
relations of the ambient module need be finitely generated.

This is Fujiwara--Kato's condition (APf), not their condition (AP), which allows
arbitrary submodules, and not the stronger shifted equality of Artin–Rees.
Nilpotent ideals satisfy the condition without any Noetherian hypothesis. The
Noetherian-ring provider is in `CoherentModules.RingTheory.Filtration`.

## Implementation notes

The predicate quantifies over modules in the ring's universe. Its eliminator
`Ideal.HasFiniteSubmoduleAdicCofinality.cofinal` applies in any module universe,
using Mathlib's `Module.Finite.reprEquiv` to transport the whole inequality.
The representative is a quotient of a finite free module by its full kernel;
no finite-presentation assumption is made.

## References

Kazuhiro Fujiwara and Fumiharu Kato, *Foundations of Rigid Geometry I*,
arXiv:1308.4734v5, §0.7.4, the (AP)/(APf) paragraph on printed page 167.
The universe bridge uses Mathlib's finite-module representatives and submodule
map, finite-generation and ideal-action APIs.
-/

@[expose] public section

universe uR uM

namespace Ideal

variable {R : Type uR} [CommRing R]

/-- The intrinsic and induced ideal-power filtrations are cofinal on every
finitely generated submodule of every finite module. This is condition (APf)
of Fujiwara--Kato, *Foundations of Rigid Geometry I*, §0.7.4.

Use `HasFiniteSubmoduleAdicCofinality.cofinal` for modules in an arbitrary
universe. The ideal need not be finitely generated, and the ambient module
need not be finitely presented. -/
def HasFiniteSubmoduleAdicCofinality (I : Ideal R) : Prop :=
  ∀ (X : Type uR) [AddCommGroup X] [Module R X] [Module.Finite R X]
    (K : Submodule R X), K.FG →
    ∀ n : ℕ, ∃ m : ℕ,
      K ⊓ ((I ^ m) • (⊤ : Submodule R X)) ≤ (I ^ n) • K

/-- The defining cofinality condition, also providing the constructor for
`HasFiniteSubmoduleAdicCofinality`. For elimination in an independent module
universe, use `HasFiniteSubmoduleAdicCofinality.cofinal`. -/
theorem hasFiniteSubmoduleAdicCofinality_iff (I : Ideal R) :
    I.HasFiniteSubmoduleAdicCofinality ↔
      ∀ (X : Type uR) [AddCommGroup X] [Module R X] [Module.Finite R X]
        (K : Submodule R X), K.FG →
        ∀ n : ℕ, ∃ m : ℕ,
          K ⊓ ((I ^ m) • (⊤ : Submodule R X)) ≤ (I ^ n) • K :=
  Iff.rfl

/-- Finite-submodule adic cofinality applies to the given module and scalar
action in any module universe, independently of the ring universe. -/
theorem HasFiniteSubmoduleAdicCofinality.cofinal
    {I : Ideal R} (hI : I.HasFiniteSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (hN : N.FG) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N := by
  let e := Module.Finite.reprEquiv R M
  let K := N.map e.symm.toLinearMap
  have hK : K.map e.toLinearMap = N :=
    (Submodule.map_symm_eq_iff e).mp rfl
  intro n
  obtain ⟨m, hm⟩ := (hasFiniteSubmoduleAdicCofinality_iff I).mp hI
    (Module.Finite.repr R M) K (hN.map e.symm.toLinearMap) n
  refine ⟨m, ?_⟩
  have hm' := Submodule.map_mono (f := e.toLinearMap) hm
  simpa only [Submodule.map_inf _ e.injective, Submodule.map_smul'', hK,
    Submodule.map_top, LinearMap.range_eq_top_of_surjective e.toLinearMap e.surjective] using hm'

/-- Nilpotent ideals have finite-submodule adic cofinality: a single vanishing
power works for every submodule and every index. No Noetherianity or finite
generation of the ideal is required. -/
theorem hasFiniteSubmoduleAdicCofinality_of_isNilpotent
    (I : Ideal R) (hI : IsNilpotent I) :
    I.HasFiniteSubmoduleAdicCofinality := by
  obtain ⟨k, hk⟩ := hI
  refine (hasFiniteSubmoduleAdicCofinality_iff I).2 ?_
  intro X _ _ _ K _ n
  refine ⟨k, ?_⟩
  rw [hk, zero_smul, Submodule.zero_eq_bot, inf_bot_eq]
  exact bot_le

end Ideal
