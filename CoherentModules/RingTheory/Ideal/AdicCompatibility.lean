/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Submodule adic cofinality

`Ideal.HasSubmoduleAdicCofinality` says that the intrinsic ideal-power filtration
of every submodule of a finite module is cofinal with the filtration induced from
the ambient module. `Ideal.HasFiniteSubmoduleAdicCofinality` restricts this
condition to finitely generated submodules. These are Fujiwara--Kato's conditions
(AP) and (APf), respectively; neither asks for the shifted equality of Artin–Rees.
Neither the ideal nor the relations of the ambient module need be finitely generated.

Full submodule adic cofinality implies finite-submodule adic cofinality.
Both conditions pass to the extension of an ideal along a module-finite algebra.
Nilpotent ideals satisfy both conditions without any Noetherian hypothesis. The
Noetherian-ring providers are in `CoherentModules.RingTheory.Filtration`.

## Implementation notes

The predicates quantify over modules in the ring's universe. Their `.cofinal`
eliminators apply in any module universe, using Mathlib's `Module.Finite.reprEquiv`
and a shared linear-equivalence transport of the whole inequality.
The representative is a quotient of a finite free module by its full kernel;
no finite-presentation assumption is made.

Finite-algebra transport uses the action composed with the algebra map.
Restriction of scalars preserves intersections and mapped ideal-power actions.
Finiteness is transitive, and finite generation of a submodule also restricts
along a module-finite algebra.

## References

Kazuhiro Fujiwara and Fumiharu Kato, *Foundations of Rigid Geometry I*,
arXiv:1308.4734v5, §0.7.4, the (AP)/(APf) paragraph on printed page 167.
The universe bridges use Mathlib's finite-module representatives and submodule
map, finite-generation and ideal-action APIs.
-/

@[expose] public section

universe uR uS uM

namespace Ideal

variable {R : Type uR} [CommRing R]

/-- The intrinsic and induced ideal-power filtrations are cofinal on every
submodule of every finite module. This is condition (AP) of Fujiwara--Kato,
*Foundations of Rigid Geometry I*, §0.7.4.

Use `HasSubmoduleAdicCofinality.cofinal` for modules in an arbitrary universe.
Neither the ideal nor the submodule need be finitely generated, and the ambient
module need not be finitely presented. -/
def HasSubmoduleAdicCofinality (I : Ideal R) : Prop :=
  ∀ (X : Type uR) [AddCommGroup X] [Module R X] [Module.Finite R X]
    (K : Submodule R X),
    ∀ n : ℕ, ∃ m : ℕ,
      K ⊓ ((I ^ m) • (⊤ : Submodule R X)) ≤ (I ^ n) • K

/-- The defining cofinality condition, also providing the constructor for
`HasSubmoduleAdicCofinality`. For elimination in an independent module universe,
use `HasSubmoduleAdicCofinality.cofinal`. -/
theorem hasSubmoduleAdicCofinality_iff (I : Ideal R) :
    I.HasSubmoduleAdicCofinality ↔
      ∀ (X : Type uR) [AddCommGroup X] [Module R X] [Module.Finite R X]
        (K : Submodule R X),
        ∀ n : ℕ, ∃ m : ℕ,
          K ⊓ ((I ^ m) • (⊤ : Submodule R X)) ≤ (I ^ n) • K :=
  Iff.rfl

private theorem cofinal_of_linearEquiv
    (I : Ideal R) {X : Type*} [AddCommGroup X] [Module R X]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (e : X ≃ₗ[R] M) (N : Submodule R M)
    (hN : ∀ n : ℕ, ∃ m : ℕ,
      N.map e.symm.toLinearMap ⊓ ((I ^ m) • (⊤ : Submodule R X)) ≤
        (I ^ n) • N.map e.symm.toLinearMap) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N := by
  have hmap : (N.map e.symm.toLinearMap).map e.toLinearMap = N :=
    (Submodule.map_symm_eq_iff e).mp rfl
  intro n
  obtain ⟨m, hm⟩ := hN n
  refine ⟨m, ?_⟩
  have hm' := Submodule.map_mono (f := e.toLinearMap) hm
  simpa only [Submodule.map_inf _ e.injective, Submodule.map_smul'', hmap,
    Submodule.map_top, LinearMap.range_eq_top_of_surjective e.toLinearMap e.surjective] using hm'

/-- Submodule adic cofinality applies to the given module and scalar action in
any module universe, independently of the ring universe. No finite generation
of the submodule is required. -/
theorem HasSubmoduleAdicCofinality.cofinal
    {I : Ideal R} (hI : I.HasSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N := by
  let e := Module.Finite.reprEquiv R M
  exact cofinal_of_linearEquiv I e N
    ((hasSubmoduleAdicCofinality_iff I).mp hI
      (Module.Finite.repr R M) (N.map e.symm.toLinearMap))

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

/-- Condition (AP) implies condition (APf) by restricting to finitely generated
submodules. -/
theorem HasSubmoduleAdicCofinality.hasFiniteSubmoduleAdicCofinality
    {I : Ideal R} (hI : I.HasSubmoduleAdicCofinality) :
    I.HasFiniteSubmoduleAdicCofinality := by
  refine (hasFiniteSubmoduleAdicCofinality_iff I).2 ?_
  intro X _ _ _ K _
  exact hI.cofinal K

/-- Finite-submodule adic cofinality applies to the given module and scalar
action in any module universe, independently of the ring universe. -/
theorem HasFiniteSubmoduleAdicCofinality.cofinal
    {I : Ideal R} (hI : I.HasFiniteSubmoduleAdicCofinality)
    {M : Type uM} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (N : Submodule R M) (hN : N.FG) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N := by
  let e := Module.Finite.reprEquiv R M
  exact cofinal_of_linearEquiv I e N
    ((hasFiniteSubmoduleAdicCofinality_iff I).mp hI
      (Module.Finite.repr R M) (N.map e.symm.toLinearMap) (hN.map e.symm.toLinearMap))

private theorem cofinal_le_of_restrictScalars
    {S : Type uS} [CommRing S] [Algebra R S]
    {M : Type uM} [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] (I : Ideal R) (N : Submodule S M) (m n : ℕ)
    (h : N.restrictScalars R ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤
      (I ^ n) • N.restrictScalars R) :
    N ⊓ (((I.map (algebraMap R S)) ^ m) • (⊤ : Submodule S M)) ≤
      ((I.map (algebraMap R S)) ^ n) • N := by
  apply (Submodule.restrictScalars_le R).mp
  simpa only [Submodule.restrictScalars_inf, ← Ideal.map_pow,
    Ideal.smul_restrictScalars, Submodule.restrictScalars_top] using h

/-- Submodule adic cofinality passes to the extension of an ideal along a
module-finite algebra. This is finite-algebra stability of condition (AP) of
Fujiwara--Kato, *Foundations of Rigid Geometry I*, §0.7.4. Neither the ideal nor
the submodules need be finitely generated. -/
theorem HasSubmoduleAdicCofinality.map
    {S : Type uS} [CommRing S] [Algebra R S] [Module.Finite R S]
    {I : Ideal R} (hI : I.HasSubmoduleAdicCofinality) :
    (I.map (algebraMap R S)).HasSubmoduleAdicCofinality := by
  refine (hasSubmoduleAdicCofinality_iff _).2 ?_
  intro X _ _ _ N n
  let : Module R X := Module.compHom X (algebraMap R S)
  let : IsScalarTower R S X := IsScalarTower.of_compHom R S X
  let : Module.Finite R X := Module.Finite.trans (R := R) S X
  obtain ⟨m, hm⟩ := hI.cofinal (N.restrictScalars R) n
  exact ⟨m, cofinal_le_of_restrictScalars I N m n hm⟩

/-- Finite-submodule adic cofinality passes to the extension of an ideal along a
module-finite algebra. This is finite-algebra stability of condition (APf) of
Fujiwara--Kato, *Foundations of Rigid Geometry I*, §0.7.4. No finite generation
of the ideal is required. -/
theorem HasFiniteSubmoduleAdicCofinality.map
    {S : Type uS} [CommRing S] [Algebra R S] [Module.Finite R S]
    {I : Ideal R} (hI : I.HasFiniteSubmoduleAdicCofinality) :
    (I.map (algebraMap R S)).HasFiniteSubmoduleAdicCofinality := by
  refine (hasFiniteSubmoduleAdicCofinality_iff _).2 ?_
  intro X _ _ _ N hN n
  let : Module R X := Module.compHom X (algebraMap R S)
  let : IsScalarTower R S X := IsScalarTower.of_compHom R S X
  let : Module.Finite R X := Module.Finite.trans (R := R) S X
  obtain ⟨m, hm⟩ := hI.cofinal (N.restrictScalars R) (hN.restrictScalars (R := R)) n
  exact ⟨m, cofinal_le_of_restrictScalars I N m n hm⟩

/-- Nilpotent ideals have submodule adic cofinality: a single vanishing power
works for every submodule and every index. No Noetherianity or finite generation
of the ideal or submodule is required. -/
theorem hasSubmoduleAdicCofinality_of_isNilpotent
    (I : Ideal R) (hI : IsNilpotent I) :
    I.HasSubmoduleAdicCofinality := by
  obtain ⟨k, hk⟩ := hI
  refine (hasSubmoduleAdicCofinality_iff I).2 ?_
  intro X _ _ _ K n
  refine ⟨k, ?_⟩
  rw [hk, zero_smul, Submodule.zero_eq_bot, inf_bot_eq]
  exact bot_le

/-- Nilpotent ideals have finite-submodule adic cofinality, as a consequence of
full submodule adic cofinality. -/
theorem hasFiniteSubmoduleAdicCofinality_of_isNilpotent
    (I : Ideal R) (hI : IsNilpotent I) :
    I.HasFiniteSubmoduleAdicCofinality :=
  (hasSubmoduleAdicCofinality_of_isNilpotent I hI).hasFiniteSubmoduleAdicCofinality

end Ideal
