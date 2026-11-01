/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Finiteness.Defs

/-!
# Clearing equality after localization for finite modules

For maps from a finitely generated semimodule, equality after localization is
witnessed by a single multiplier from the localizing submonoid. The multiplier
is obtained on a finite generating family and then extended by linearity.

This extends the finite-source equality-clearing implication
`Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule` from Mathlib's
commutative-ring and additive-group setting to commutative semirings and additive
monoids, and includes its converse.
-/

@[expose] public section

universe uR uP uM uN

namespace IsLocalizedModule

/-- Two maps from a finitely generated semimodule become equal after localization
if and only if one multiplier from the localizing submonoid makes them equal. -/
theorem comp_eq_iff_exists_smul_eq
    {R : Type uR} [CommSemiring R] (S : Submonoid R)
    {P : Type uP} [AddCommMonoid P] [Module R P] [Module.Finite R P]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    {N : Type uN} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (g₁ g₂ : P →ₗ[R] M) :
    f.comp g₁ = f.comp g₂ ↔ ∃ s : S, s • g₁ = s • g₂ := by
  constructor
  · intro h
    obtain ⟨n, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := P)
    have hclear : ∀ t : Finset (Fin n),
        ∃ s : S, ∀ i ∈ t, s • g₁ (v i) = s • g₂ (v i) := by
      intro t
      induction t using Finset.induction_on with
      | empty => exact ⟨1, by simp⟩
      | @insert i t _ ih =>
        obtain ⟨a, ha⟩ := (IsLocalizedModule.eq_iff_exists S f).mp
          (congrArg (fun k : P →ₗ[R] N => k (v i)) h)
        obtain ⟨b, hb⟩ := ih
        refine ⟨a * b, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · simpa only [← mul_smul, mul_comm] using
            congrArg (fun y : M => b • y) ha
        · simpa only [mul_smul] using
            congrArg (fun y : M => a • y) (hb j hj)
    obtain ⟨s, hs⟩ := hclear Finset.univ
    refine ⟨s, LinearMap.ext_on_range hv ?_⟩
    intro i
    exact hs i (Finset.mem_univ i)
  · rintro ⟨s, hs⟩
    apply LinearMap.ext
    intro x
    exact (IsLocalizedModule.eq_iff_exists S f).mpr
      ⟨s, congrArg (fun k : P →ₗ[R] M => k x) hs⟩

end IsLocalizedModule
