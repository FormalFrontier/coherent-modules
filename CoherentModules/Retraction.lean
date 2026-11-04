/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Coherence along semilinear retractions

Coherence descends through compatible one-sided retractions of coefficient rings and modules.
The rings may be noncommutative, and the modules retain their given additive commutative monoids
and scalar actions. The two rings and two module carriers have independent universes.

## Main declarations

* `Module.IsCoherent.of_semilinear_retract`: descent of module coherence along semilinear
  retractions.
* `IsCoherentRing.of_retract`: a retract of a coherent ring is coherent.

## Proof approach and references

The proof uses this library's `Module.IsCoherent.iff_finite_and_fg_ker` kernel criterion.
A finite row over the smaller ring extends to a linear combination over the larger ring.
Its kernel maps semilinearly and surjectively onto the original row kernel. The coordinate
maps use Mathlib's `Finsupp.mapRange.linearMap` and `Finsupp.linearEquivFunOnFinite`, with the
original pointwise actions. The row calculations use Mathlib's finite-function expansion and
`Fintype.linearCombination`, and finite generation descends by `Module.Finite.of_surjective`.
-/

@[expose] public section

universe uR uS uN uM

namespace Module.IsCoherent

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable {N : Type uN} {M : Type uM}
variable [AddCommMonoid N] [AddCommMonoid M] [Module R N] [Module S M]

/-- Coherence descends along a semilinear module retraction whose coefficient maps also
form a retraction. Both left-inverse conditions are one-sided; no additional scalar actions,
scalar finiteness or flatness assumptions are required. -/
theorem of_semilinear_retract (σ : R →+* S) (τ : S →+* R)
    (f : N →ₛₗ[σ] M) (g : M →ₛₗ[τ] N)
    (hRing : Function.LeftInverse τ σ) (hModule : Function.LeftInverse g f)
    [Module.IsCoherent S M] : Module.IsCoherent R N := by
  classical
  apply (Module.IsCoherent.iff_finite_and_fg_ker (R := R) (M := N)).2
  refine ⟨Module.Finite.of_surjective g (fun x ↦ ⟨f x, hModule x⟩), ?_⟩
  intro n h
  let H : (Fin n → S) →ₗ[S] M :=
    Fintype.linearCombination S (fun i ↦ f (h (Pi.single i 1)))
  have hH : (LinearMap.ker H).FG :=
    ((Module.IsCoherent.iff_finite_and_fg_ker (R := S) (M := M)).1 inferInstance).2 n H
  let E_R := Finsupp.linearEquivFunOnFinite R R (Fin n)
  let E_S := Finsupp.linearEquivFunOnFinite S S (Fin n)
  let T : (Fin n → S) →ₛₗ[τ] (Fin n → R) :=
    E_R.toLinearMap.comp
      ((Finsupp.mapRange.linearMap τ.toSemilinearMap).comp E_S.symm.toLinearMap)
  let U : (Fin n → R) →ₛₗ[σ] (Fin n → S) :=
    E_S.toLinearMap.comp
      ((Finsupp.mapRange.linearMap σ.toSemilinearMap).comp E_R.symm.toLinearMap)
  have T_apply (a : Fin n → S) (i : Fin n) : T a i = τ (a i) := by
    simp [T, E_R, E_S]
  have U_apply (b : Fin n → R) (i : Fin n) : U b i = σ (b i) := by
    simp [U, E_R, E_S]
  -- Expand the original row without changing any of its scalar actions.
  have hrow (b : Fin n → R) : h b = ∑ i, b i • h (Pi.single i 1) := by
    calc
      h b = h (∑ i, Pi.single i (b i)) :=
        congrArg h (LinearMap.sum_single_apply (fun _ : Fin n ↦ R) b).symm
      _ = ∑ i, h (Pi.single i (b i)) := by rw [map_sum]
      _ = ∑ i, b i • h (Pi.single i 1) := by
        apply Finset.sum_congr rfl
        intro i _
        simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using
          h.map_smul (b i) (Pi.single i (1 : R))
  have hT (a : Fin n → S) : h (T a) = g (H a) := by
    rw [hrow]
    simp only [H, Fintype.linearCombination_apply, map_sum, g.map_smulₛₗ, T_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [hModule (h (Pi.single i 1))]
  have hU (b : Fin n → R) : H (U b) = f (h b) := by
    rw [hrow b]
    simp only [H, Fintype.linearCombination_apply, map_sum, f.map_smulₛₗ, U_apply]
  have hmaps : ∀ a ∈ LinearMap.ker H, T a ∈ LinearMap.ker h := by
    intro a ha
    rw [LinearMap.mem_ker] at ha ⊢
    rw [hT, ha, map_zero]
  let t : LinearMap.ker H →ₛₗ[τ] LinearMap.ker h := T.restrict hmaps
  have ht : Function.Surjective t := by
    intro b
    have hb : U (b : Fin n → R) ∈ LinearMap.ker H := by
      rw [LinearMap.mem_ker, hU, LinearMap.mem_ker.mp b.property, map_zero]
    refine ⟨⟨U b, hb⟩, ?_⟩
    apply Subtype.ext
    simp only [t, LinearMap.coe_restrict_apply]
    ext i
    rw [T_apply, U_apply, hRing]
  let _ : Module.Finite S (LinearMap.ker H) := Module.Finite.of_fg hH
  let _ : Module.Finite R (LinearMap.ker h) := Module.Finite.of_surjective t ht
  exact Submodule.FG.of_finite

end Module.IsCoherent

/-- A ring retract of a coherent ring is coherent. The rings may be noncommutative and have
independent universes, and only the composite from the smaller ring back to itself is required
to be the identity. -/
theorem IsCoherentRing.of_retract {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (σ : R →+* S) (τ : S →+* R) (hRing : Function.LeftInverse τ σ)
    [IsCoherentRing S] : IsCoherentRing R :=
  ⟨Module.IsCoherent.of_semilinear_retract σ τ σ.toSemilinearMap τ.toSemilinearMap
    hRing hRing⟩
