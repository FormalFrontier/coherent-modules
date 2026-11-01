/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Ideal.AdicCompatibility
public import Mathlib.RingTheory.LocalProperties.Submodule

/-!
# Adic cofinality near the closed locus

Submodule adic cofinality, and its finite-submodule variant, can be checked after
principal localization at the elements of any set `s` satisfying
`I ⊔ Ideal.span s = ⊤`. Thus the distinguished opens need only cover `V(I)`,
not the whole spectrum. These are not stalkwise criteria.

Full submodule adic cofinality allows arbitrary submodules of finite modules;
the finite-submodule variant requires only the submodule to be finitely generated.
Neither result requires the ideal to be finitely generated or the ambient module
to be finitely presented.

## Implementation notes

For one module, submodule and target stage, augment `s` by the elements of `I`
and extract a finite unit-span subset. The extended ideal is top on the added
charts. A finite supremum of local cutoffs then works on every selected chart.
Mathlib's localized-submodule identities and inclusion reflection give the
inclusion for the same two global submodules. This shared argument works for
semimodules over commutative semirings, without any finiteness hypothesis.
The cutoffs are pointwise in the module, submodule and target stage; there is
no uniform shift or uniform denominator bound.

The original scalar action is retained. Canonical localized modules are finite
over the localized ring, not necessarily over the original ring, and the
universe-polymorphic `.cofinal` interfaces apply to these modules.

## References

The predicates are Fujiwara--Kato's conditions (AP) and (APf), as documented in
`CoherentModules.RingTheory.Ideal.AdicCompatibility`.
The locality proofs reuse Andrew Yang's submodule-localization formalization, Andrew Yang
and David Swinarski's submodule inclusion reflection, and Christian Merten's
localization finiteness API in Mathlib.
-/

@[expose] public section

universe uR uM

namespace Ideal

private theorem exists_adic_cutoff_of_forall_map_away
    {R : Type uR} [CommSemiring R]
    {M : Type uM} [AddCommMonoid M] [Module R M]
    (I : Ideal R) (N : Submodule R M) (s : Set R)
    (hcover : I ⊔ Ideal.span s = ⊤) (n : ℕ)
    (hlocal : ∀ f ∈ s, ∃ m : ℕ,
      N.localized (Submonoid.powers f) ⊓
          (((I.map (algebraMap R (Localization.Away f))) ^ m) • ⊤) ≤
        ((I.map (algebraMap R (Localization.Away f))) ^ n) •
          N.localized (Submonoid.powers f)) :
    ∃ m : ℕ, N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N := by
  classical
  have hspan : Ideal.span (s ∪ (I : Set R)) = ⊤ := by
    rw [Ideal.span_union, Ideal.span_eq, sup_comm]
    exact hcover
  obtain ⟨t, ht, htspan⟩ :=
    (Ideal.span_eq_top_iff_finite (s ∪ (I : Set R))).mp hspan
  have hcut : ∀ f : t, ∃ m : ℕ,
      N.localized (Submonoid.powers f.1) ⊓
          (((I.map (algebraMap R (Localization.Away f.1))) ^ m) • ⊤) ≤
        ((I.map (algebraMap R (Localization.Away f.1))) ^ n) •
          N.localized (Submonoid.powers f.1) := by
    intro f
    rcases ht f.2 with hf | hf
    · exact hlocal f.1 hf
    · have htop : I.map (algebraMap R (Localization.Away f.1)) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
          (IsLocalization.Away.algebraMap_isUnit f.1)
      refine ⟨0, ?_⟩
      simpa only [htop, Ideal.top_pow, Submodule.top_smul, inf_top_eq] using
        (le_refl (N.localized (Submonoid.powers f.1)))
  choose k hk using hcut
  refine ⟨t.attach.sup k, ?_⟩
  apply Submodule.le_of_isLocalized_span (t : Set R) htspan
    (fun f ↦ LocalizedModule.Away f.1 M)
    (fun f ↦ LocalizedModule.mkLinearMap (Submonoid.powers f.1) M)
  intro f
  have hkm : k f ≤ t.attach.sup k := Finset.le_sup (t.mem_attach f)
  have hpow :
      (I.map (algebraMap R (Localization.Away f.1))) ^ (t.attach.sup k) ≤
        (I.map (algebraMap R (Localization.Away f.1))) ^ (k f) :=
    Ideal.pow_le_pow_right hkm
  have hstage :
      N.localized (Submonoid.powers f.1) ⊓
          (((I.map (algebraMap R (Localization.Away f.1))) ^ (t.attach.sup k)) • ⊤) ≤
        ((I.map (algebraMap R (Localization.Away f.1))) ^ n) •
          N.localized (Submonoid.powers f.1) :=
    (inf_le_inf_left _ (Submodule.smul_mono_left hpow)).trans (hk f)
  have hloc :
      (N ⊓ ((I ^ (t.attach.sup k)) • (⊤ : Submodule R M))).localized'
          (Localization.Away f.1) (Submonoid.powers f.1)
          (LocalizedModule.mkLinearMap (Submonoid.powers f.1) M) ≤
        ((I ^ n) • N).localized' (Localization.Away f.1) (Submonoid.powers f.1)
          (LocalizedModule.mkLinearMap (Submonoid.powers f.1) M) := by
    simpa only [Submodule.localized'_inf, Submodule.localized'_smul,
      Submodule.localized'_top, Ideal.localized'_eq_map, Ideal.map_pow] using hstage
  simpa only [Submodule.restrictScalars_localized'] using
    (Submodule.restrictScalars_le R).mpr hloc

/-- Submodule adic cofinality is equivalent to submodule adic cofinality after
principal localization on a distinguished-open cover of `V(I)`. The set of
localizing elements may be arbitrary, and every submodule of every finite
ambient module is allowed. -/
theorem hasSubmoduleAdicCofinality_iff_forall_map_away
    {R : Type uR} [CommRing R] (I : Ideal R) (s : Set R)
    (hcover : I ⊔ Ideal.span s = ⊤) :
    I.HasSubmoduleAdicCofinality ↔
      ∀ f ∈ s,
        (I.map (algebraMap R (Localization.Away f))).HasSubmoduleAdicCofinality := by
  constructor
  · intro hI f _
    exact hI.map_of_isLocalization (Submonoid.powers f)
  · intro hlocal
    refine (hasSubmoduleAdicCofinality_iff I).2 ?_
    intro M _ _ _ N n
    apply exists_adic_cutoff_of_forall_map_away I N s hcover n
    intro f hf
    exact (hlocal f hf).cofinal (N.localized (Submonoid.powers f)) n

/-- Finite-submodule adic cofinality is equivalent to its counterpart after
principal localization on a distinguished-open cover of `V(I)`. Only the
submodule is required to be finitely generated; neither the ideal nor the
relations of the finite ambient module need be finitely generated. -/
theorem hasFiniteSubmoduleAdicCofinality_iff_forall_map_away
    {R : Type uR} [CommRing R] (I : Ideal R) (s : Set R)
    (hcover : I ⊔ Ideal.span s = ⊤) :
    I.HasFiniteSubmoduleAdicCofinality ↔
      ∀ f ∈ s,
        (I.map (algebraMap R (Localization.Away f))).HasFiniteSubmoduleAdicCofinality := by
  constructor
  · intro hI f _
    exact hI.map_of_isLocalization (Submonoid.powers f)
  · intro hlocal
    refine (hasFiniteSubmoduleAdicCofinality_iff I).2 ?_
    intro M _ _ _ N hN n
    apply exists_adic_cutoff_of_forall_map_away I N s hcover n
    intro f hf
    exact (hlocal f hf).cofinal (N.localized (Submonoid.powers f))
      (Submodule.localized'_fg (Localization.Away f) (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M) hN) n

end Ideal
