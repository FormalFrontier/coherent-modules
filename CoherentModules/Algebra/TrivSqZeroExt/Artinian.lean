/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.TrivSqZeroExt.Kernel
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.RingTheory.Artinian.Module

/-!
# Artinian trivial square-zero extensions

A trivial square-zero extension is left Artinian exactly when its base ring is left Artinian
and its coefficient bimodule is Artinian as a left module. The compatible right action need
not be central.

The coefficient module is assumed only to be an additive commutative monoid; its additive
group structure is derived from the left action of the base ring.

## References

The proof follows the projection-kernel and regular-action tower arguments in
`CoherentModules.Algebra.TrivSqZeroExt.Noetherian`, using Mathlib's theorems transferring
Artinianity through linear injections, bijective semilinear maps, surjective ring
homomorphisms, and scalar towers.
-/

@[expose] public section

universe uR uM

namespace TrivSqZeroExt

/-- A trivial square-zero extension is left Artinian precisely when its base ring is left
Artinian and its coefficient module is Artinian as a left module over the base ring. -/
theorem isArtinianRing_iff
    {R : Type uR} {M : Type uM} [Ring R] [AddCommMonoid M]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] :
    IsArtinianRing (TrivSqZeroExt R M) ↔ IsArtinianRing R ∧ IsArtinian R M := by
  let S := TrivSqZeroExt R M
  let σ : S →+* R := fstHom ℕ R M
  have hσ : Function.Surjective σ := fun r ↦ ⟨inl r, rfl⟩
  constructor
  · intro h
    have : IsArtinianRing S := h
    have hR : IsArtinianRing R := hσ.isArtinianRing
    have : IsArtinian S (RingHom.ker σ) :=
      isArtinian_of_injective (RingHom.ker σ).subtype Subtype.val_injective
    have : RingHomSurjective σ := ⟨hσ⟩
    have hM : IsArtinian R M :=
      (LinearMap.isArtinian_iff_of_bijective (kerFstHomSnd R M)
        (kerFstHomSnd_bijective R M)).mp inferInstance
    exact ⟨hR, hM⟩
  · rintro ⟨hR, hM⟩
    have : IsArtinianRing R := hR
    have : IsArtinian R M := hM
    let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
    have hS : IsArtinian R S := inferInstanceAs (IsArtinian R (R × M))
    have : IsScalarTower R S S :=
      ⟨fun r x y => by
        change (r • x) * y = r • (x * y)
        rw [← inl_mul_eq_smul, ← inl_mul_eq_smul, mul_assoc]⟩
    exact isArtinian_of_tower R hS

end TrivSqZeroExt
