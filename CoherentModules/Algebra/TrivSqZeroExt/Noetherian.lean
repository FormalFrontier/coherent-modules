/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.TrivSqZeroExt.Finite
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Noetherianity of trivial square-zero extensions

For an associative ring `R` and an `R`-bimodule `M`, the trivial square-zero
extension is left Noetherian if and only if `R` is left Noetherian and `M` is
finitely generated as a left `R`-module. Equivalently, both `R` and `M` are
Noetherian on the left over `R`.

No commutativity of `R` or centrality of the bimodule is required. The kernel
of the first projection identifies with `M` by its second coordinate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section

namespace TrivSqZeroExt

universe uR uM

/-- The projection kernel is Noetherian over the extension precisely when its
coefficient module is Noetherian over the base semiring. -/
private theorem isNoetherian_ker_fstHom_iff
    (R : Type uR) (M : Type uM) [Semiring R] [AddCommMonoid M]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] :
    IsNoetherian (TrivSqZeroExt R M)
        (RingHom.ker ((TrivSqZeroExt.fstHom ℕ R M).toRingHom)) ↔
      IsNoetherian R M := by
  let σ : TrivSqZeroExt R M →+* R := (fstHom ℕ R M).toRingHom
  let : RingHomSurjective σ := ⟨fun r ↦ ⟨inl r, rfl⟩⟩
  let f : RingHom.ker σ →ₛₗ[σ] M :=
    { toFun := fun x ↦ (x : TrivSqZeroExt R M).snd
      map_add' := fun x y ↦ snd_add (x : TrivSqZeroExt R M) y
      map_smul' := by
        intro a x
        have hx : (x : TrivSqZeroExt R M).fst = 0 := x.property
        change (a * (x : TrivSqZeroExt R M)).snd = a.fst • (x : TrivSqZeroExt R M).snd
        simp [snd_mul, hx] }
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Subtype.ext
      apply TrivSqZeroExt.ext
      · have hx : (x : TrivSqZeroExt R M).fst = 0 := x.property
        have hy : (y : TrivSqZeroExt R M).fst = 0 := y.property
        exact hx.trans hy.symm
      · exact h
    · intro m
      exact ⟨⟨inr m, rfl⟩, rfl⟩
  exact LinearMap.isNoetherian_iff_of_bijective f hf

example :
    IsNoetherian (TrivSqZeroExt ℕ ℕ)
        (RingHom.ker ((TrivSqZeroExt.fstHom ℕ ℕ ℕ).toRingHom)) ↔
      IsNoetherian ℕ ℕ :=
  isNoetherian_ker_fstHom_iff ℕ ℕ

variable {R : Type uR} {M : Type uM} [Ring R] [AddCommMonoid M]
  [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]

private theorem isNoetherianRing_of_base_finite
    (h : IsNoetherianRing R ∧ Module.Finite R M) :
    IsNoetherianRing (TrivSqZeroExt R M) := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  let : IsNoetherianRing R := h.1
  let : Module.Finite R M := h.2
  let : IsNoetherian R M := inferInstance
  have hExt : IsNoetherian R (TrivSqZeroExt R M) :=
    inferInstanceAs (IsNoetherian R (R × M))
  let : IsScalarTower R (TrivSqZeroExt R M) (TrivSqZeroExt R M) :=
    ⟨fun r x y => by
      change (r • x) * y = r • (x * y)
      rw [← inl_mul_eq_smul, ← inl_mul_eq_smul, mul_assoc]⟩
  exact isNoetherian_of_tower R hExt

/-- A trivial square-zero extension is left Noetherian precisely when its base
ring is left Noetherian and its coefficient module is finitely generated as a
left module over the base ring. -/
theorem isNoetherianRing_iff :
    IsNoetherianRing (TrivSqZeroExt R M) ↔ IsNoetherianRing R ∧ Module.Finite R M := by
  constructor
  · intro h
    let : IsNoetherianRing (TrivSqZeroExt R M) := h
    have hR : IsNoetherianRing R :=
      isNoetherianRing_of_surjective (TrivSqZeroExt R M) R
        (fstHom ℕ R M).toRingHom fst_surjective
    have hM : IsNoetherian R M :=
      (isNoetherian_ker_fstHom_iff R M).mp inferInstance
    let : IsNoetherian R M := hM
    exact ⟨hR, Module.IsNoetherian.finite R M⟩
  · exact isNoetherianRing_of_base_finite

/-- A trivial square-zero extension is left Noetherian precisely when its base
ring and its coefficient module are both Noetherian on the left over the base
ring. -/
theorem isNoetherianRing_iff_isNoetherian :
    IsNoetherianRing (TrivSqZeroExt R M) ↔ IsNoetherianRing R ∧ IsNoetherian R M := by
  constructor
  · intro h
    have h' := isNoetherianRing_iff.mp h
    let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    let : IsNoetherianRing R := h'.1
    let : Module.Finite R M := h'.2
    exact ⟨h'.1, inferInstance⟩
  · intro h
    let : IsNoetherian R M := h.2
    exact isNoetherianRing_iff.mpr ⟨h.1, Module.IsNoetherian.finite R M⟩

end TrivSqZeroExt
