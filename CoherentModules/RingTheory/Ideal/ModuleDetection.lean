/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Ideal.Annihilator
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Detection of module maps by nilpotent ideals

Restriction to the common annihilator of a nilpotent two-sided ideal detects
injectivity of linear maps between additive groups. Reduction modulo a nilpotent
left ideal detects surjectivity, without any finite-generation hypothesis.
The latter follows by applying uniform nilpotence to the cokernel.

The common-annihilator map is a restriction of the given map. The quotient map
is Mathlib's `Submodule.mapQ`, on the quotients by `I • ⊤`.
-/

@[expose] public section

universe u v w z

namespace Ideal

variable {A : Type u} [Semiring A]
variable {V : Type v} [AddCommMonoid V] [Module A V]
variable {W : Type w} [AddCommMonoid W] [Module A W]
variable {X : Type z} [AddCommMonoid X] [Module A X]

/-- The restriction of a linear map to the common annihilators of a two-sided ideal. -/
def annihilatorSubmoduleMap (I : Ideal A) [I.IsTwoSided] (f : V →ₗ[A] W) :
    annihilatorSubmodule V I →ₗ[A] annihilatorSubmodule W I :=
  f.restrict fun x hx a ha => by
    change a • f x = 0
    rw [← f.map_smul, (mem_annihilatorSubmodule_iff.mp hx) a ha, f.map_zero]

/-- Restriction acts by the original linear map on the underlying vector. -/
@[simp]
theorem annihilatorSubmoduleMap_apply (I : Ideal A) [I.IsTwoSided]
    (f : V →ₗ[A] W) (x : annihilatorSubmodule V I) :
    (annihilatorSubmoduleMap I f x : W) = f x := rfl

/-- Restriction preserves the identity map. -/
@[simp]
theorem annihilatorSubmoduleMap_id (I : Ideal A) [I.IsTwoSided] :
    annihilatorSubmoduleMap I (LinearMap.id : V →ₗ[A] V) = LinearMap.id := by
  ext x
  rfl

/-- Restriction preserves composition. -/
@[simp]
theorem annihilatorSubmoduleMap_comp (I : Ideal A) [I.IsTwoSided]
    (f : V →ₗ[A] W) (g : W →ₗ[A] X) :
    annihilatorSubmoduleMap I (g.comp f) =
      (annihilatorSubmoduleMap I g).comp (annihilatorSubmoduleMap I f) := by
  ext x
  rfl

end Ideal

namespace Submodule

variable {A : Type u} [Semiring A]
variable {V : Type v} [AddCommMonoid V] [Module A V]

/-- Nilpotent Nakayama: a submodule equal to its product by a nilpotent left
ideal is zero. No finite-generation or additive-cancellation assumption is needed. -/
theorem eq_bot_of_isNilpotent_of_smul_eq_self (I : Ideal A) (hI : IsNilpotent I)
    (N : Submodule A V) (hN : I • N = N) : N = ⊥ := by
  apply le_antisymm ?_ bot_le
  exact le_of_le_sup_smul_of_isNilpotent hI
    (by simpa only [bot_sup_eq, hN] using (le_refl N))

end Submodule

namespace LinearMap

section AdditiveGroups
variable {A : Type u} [Semiring A]
variable {V : Type v} [AddCommGroup V] [Module A V]
variable {W : Type w} [AddCommGroup W] [Module A W]

/-- A nilpotent two-sided ideal detects genuine injectivity on its common
annihilator. Additive groups ensure that a zero kernel implies injectivity. -/
theorem injective_iff_annihilatorSubmoduleMap (I : Ideal A) [I.IsTwoSided]
    (hI : IsNilpotent I) (f : V →ₗ[A] W) :
    Function.Injective f ↔ Function.Injective (I.annihilatorSubmoduleMap f) := by
  constructor
  · intro hf x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  · intro hf
    have hker : f.ker = ⊥ := by
      by_contra hker
      let : Nontrivial f.ker := Submodule.nontrivial_iff_ne_bot.mpr hker
      obtain ⟨x, hx, hxI⟩ := Ideal.exists_ne_zero_le_torsionOf_of_isNilpotent
        (V := f.ker) I hI
      have hmem : (x : V) ∈ Ideal.annihilatorSubmodule V I := by
        intro a ha
        exact congrArg Subtype.val ((Ideal.mem_torsionOf_iff x a).mp (hxI ha))
      have hz : I.annihilatorSubmoduleMap f ⟨x, hmem⟩ = 0 := by
        apply Subtype.ext
        exact x.property
      have hz' : I.annihilatorSubmoduleMap f ⟨x, hmem⟩ =
          I.annihilatorSubmoduleMap f 0 := hz.trans (map_zero _).symm
      have hx0 : (x : V) = 0 := congrArg Subtype.val (hf hz')
      exact hx (Subtype.ext hx0)
    intro x y hxy
    have hsub : x - y ∈ f.ker := by
      change f (x - y) = 0
      rw [map_sub, hxy, sub_self]
    simpa only [hker, Submodule.mem_bot, sub_eq_zero] using hsub
end AdditiveGroups

section Ring
variable {A : Type u} [Ring A]
variable {V : Type v} [AddCommGroup V] [Module A V]
variable {W : Type w} [AddCommGroup W] [Module A W]

/-- Reduction modulo a nilpotent left ideal detects surjectivity of every
linear map. The map on quotients is the usual `Submodule.mapQ`. -/
theorem surjective_iff_mapQ_smul_top (I : Ideal A) (hI : IsNilpotent I)
    (f : V →ₗ[A] W) :
    Function.Surjective f ↔ Function.Surjective
      ((I • (⊤ : Submodule A V)).mapQ (I • (⊤ : Submodule A W)) f
        (Submodule.smul_top_le_comap_smul_top I f)) := by
  simp only [← LinearMap.range_eq_top, Submodule.range_mapQ, Submodule.map_mkQ_eq_top]
  constructor
  · intro hf
    simp [hf]
  · intro hf
    have hquot : I • (⊤ : Submodule A (W ⧸ f.range)) = ⊤ := by
      calc
        I • (⊤ : Submodule A (W ⧸ f.range)) =
            (I • (⊤ : Submodule A W)).map f.range.mkQ := by
          rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
        _ = ⊤ := (Submodule.map_mkQ_eq_top _ _).mpr
          (by simpa only [sup_comm] using hf)
    have hzero := Submodule.eq_bot_of_isNilpotent_of_smul_eq_self I hI
      (⊤ : Submodule A (W ⧸ f.range)) hquot
    have hmap : f.range.map f.range.mkQ = ⊤ := by
      rw [Submodule.mkQ_map_self, ← hzero]
    simpa using (Submodule.map_mkQ_eq_top _ _).mp hmap
end Ring

end LinearMap
