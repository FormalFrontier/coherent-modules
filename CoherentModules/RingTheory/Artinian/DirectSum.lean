/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Order.CompactlyGenerated.Basic
public import Mathlib.RingTheory.Artinian.Module

/-!
# Artinian direct sums

An arbitrary direct sum of modules over a ring is Artinian if and only if every
summand is Artinian and only finitely many summands are nontrivial. The ring need
not be commutative, and the summands need only be additive commutative monoids.
Their additive group structures are obtained from their original module actions.

## References

The proof uses Mathlib's coordinate inclusions and evaluations for direct sums,
`WellFoundedLT.finite_ne_bot_of_iSupIndep` for the necessary finiteness condition,
and `isArtinian_pi` together with `isArtinian_of_injective` for sufficiency.
The finite product is taken over the subtype of nontrivial summands, using the
public constructor `LinearMap.pi` and the original coordinate modules.
-/

@[expose] public section

universe uR uI uM

open scoped DirectSum

namespace DirectSum

private theorem iSupIndep_range_lof
    {R : Type uR} {ι : Type uI} {M : ι → Type uM}
    [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [DecidableEq ι] :
    iSupIndep (fun i => LinearMap.range (lof R ι M i)) := by
  rw [iSupIndep_def]
  intro i
  have hker :
      (⨆ (j) (_ : j ≠ i), LinearMap.range (lof R ι M j)) ≤
        LinearMap.ker (DFinsupp.lapply (R := R) (M := M) i) := by
    refine iSup_le fun j => iSup_le fun hji => ?_
    rintro _ ⟨x, rfl⟩
    rw [LinearMap.mem_ker, DFinsupp.lapply_apply, lof_eq_of]
    exact of_eq_of_ne j i x hji.symm
  refine Submodule.disjoint_def.mpr ?_
  rintro _ ⟨x, rfl⟩ hx
  have hx0 : x = 0 := by
    have hx' := hker hx
    rw [LinearMap.mem_ker, DFinsupp.lapply_apply, lof_eq_of, of_eq_same] at hx'
    exact hx'
  simp only [hx0, map_zero]

private theorem range_lof_ne_bot_iff
    {R : Type uR} {ι : Type uI} {M : ι → Type uM}
    [Semiring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [DecidableEq ι] (i : ι) :
    LinearMap.range (lof R ι M i) ≠ ⊥ ↔ Nontrivial (M i) := by
  have hInjective : Function.Injective (lof R ι M i) := of_injective (β := M) i
  constructor
  · intro hi
    by_contra hM
    let : Subsingleton (M i) := not_nontrivial_iff_subsingleton.mp hM
    apply hi
    rw [LinearMap.range_eq_bot]
    apply LinearMap.ext
    intro x
    exact (congrArg (lof R ι M i) (Subsingleton.elim x 0)).trans (map_zero _)
  · intro hM hbot
    let : Nontrivial (M i) := hM
    obtain ⟨x, hx⟩ := exists_ne (0 : M i)
    have hzero : lof R ι M i = 0 := LinearMap.range_eq_bot.mp hbot
    exact hx (hInjective (by simp only [hzero, LinearMap.zero_apply]))

/-- A direct sum over a ring is Artinian exactly when each summand is Artinian and
only finitely many summands are nontrivial. The summands need only be additive
commutative monoids with their given module structures. -/
theorem isArtinian_iff
    {R : Type uR} {ι : Type uI} {M : ι → Type uM}
    [Ring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)] :
    IsArtinian R (⨁ i, M i) ↔
      (∀ i, IsArtinian R (M i)) ∧ Set.Finite {i : ι | Nontrivial (M i)} := by
  classical
  constructor
  · intro h
    have : IsArtinian R (⨁ i, M i) := h
    refine ⟨?_, ?_⟩
    · intro i
      exact isArtinian_of_injective (lof R ι M i) (of_injective (β := M) i)
    · have hFin := WellFoundedLT.finite_ne_bot_of_iSupIndep
        (iSupIndep_range_lof (R := R) (ι := ι) (M := M))
      simpa only [range_lof_ne_bot_iff] using hFin
  · rintro ⟨hArt, hFin⟩
    let q : (⨁ i, M i) →ₗ[R] (∀ i : {i : ι // Nontrivial (M i)}, M i.val) :=
      LinearMap.pi (fun i : {i : ι // Nontrivial (M i)} =>
        DFinsupp.lapply (R := R) (M := M) i.val)
    have hq : Function.Injective q := by
      intro x y hxy
      apply DFinsupp.injective_pi_lapply (R := R) (M := M)
      funext i
      by_cases hi : Nontrivial (M i)
      · exact congr_fun hxy ⟨i, hi⟩
      · let : Subsingleton (M i) := not_nontrivial_iff_subsingleton.mp hi
        exact Subsingleton.elim _ _
    let : Finite {i : ι // Nontrivial (M i)} := hFin.to_subtype
    let : ∀ i : {i : ι // Nontrivial (M i)}, IsArtinian R (M i.val) :=
      fun i => hArt i.val
    let : ∀ i, AddCommGroup (M i) :=
      fun i => Module.addCommMonoidToAddCommGroup R (M := M i)
    exact isArtinian_of_injective q hq

end DirectSum
