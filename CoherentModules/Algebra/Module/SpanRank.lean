/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Generators of semilinear images

Taking the span over the target semiring allows generator bounds for a semilinear map
without assuming that its scalar homomorphism is surjective. The cardinal bound applies to
arbitrary submodules. The natural-valued bound assumes finite generation of the source.

For each element of a target submodule, consider the scalars that multiply it into
the image. If these scalars generate the unit left ideal, the target submodule equals
the target-scalar span of its comap image. Finite generation therefore ascends from
the comap under this pointwise unimodular condition. A single clearing scalar with a
left inverse is sufficient, recovering the existing left-inverse and unit criteria.
Neither Noetherianity nor surjectivity of the scalar homomorphism is required.

The scalar-span step reuses Mathlib's `Submodule.mem_of_span_top_of_smul_mem` from
ideal operations, credited to Kenny Lau. The semilinear argument extends this library's
finite-generation clearing criteria and uses `Submodule.FG.span_image`.
-/

@[expose] public section

universe uR uS uM uN

namespace Submodule

variable {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module S N] {σ : R →+* S}

/-- Spanning before taking a semilinear image does not change its target-scalar span. -/
lemma span_image_span (f : M →ₛₗ[σ] N) (s : Set M) :
    span S (f '' (span R s : Set M)) = span S (f '' s) := by
  apply le_antisymm
  · exact span_le.mpr (image_span_subset_span f s)
  · apply span_mono
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, subset_span hx, rfl⟩

/-- The target-scalar span of a semilinear image needs no more generators than its source.
The lifts compare generator cardinals in independent module universes. -/
lemma lift_spanRank_span_image_le (f : M →ₛₗ[σ] N) (p : Submodule R M) :
    Cardinal.lift.{uM} (span S (f '' (p : Set M))).spanRank ≤
      Cardinal.lift.{uN} p.spanRank := by
  obtain ⟨s, hcard, hspan⟩ := p.exists_span_set_card_eq_spanRank
  have himage : span S (f '' (p : Set M)) = span S (f '' s) := by
    rw [← hspan, span_image_span]
  rw [himage]
  calc
    Cardinal.lift.{uM} (span S (f '' s)).spanRank ≤
        Cardinal.lift.{uM} (Cardinal.mk (f '' s)) :=
      Cardinal.lift_le.mpr (spanRank_span_le_card (f '' s))
    _ ≤ Cardinal.lift.{uN} (Cardinal.mk s) := Cardinal.mk_image_le_lift
    _ = Cardinal.lift.{uN} p.spanRank := congrArg Cardinal.lift hcard

/-- The target-scalar span of the image of a finitely generated submodule is finitely generated. -/
lemma FG.span_image {p : Submodule R M} (hp : p.FG) (f : M →ₛₗ[σ] N) :
    (span S (f '' (p : Set M))).FG := by
  classical
  obtain ⟨s, _, hs⟩ := hp.exists_span_finset_card_eq_spanFinrank
  refine ⟨s.image f, ?_⟩
  rw [Finset.coe_image, ← span_image_span, hs]

/-- For a finitely generated source, a semilinear image has no larger minimum finite number
of generators. Finite generation is necessary because `spanFinrank` is zero for an
infinitely generated submodule. -/
lemma spanFinrank_span_image_le_of_fg (f : M →ₛₗ[σ] N) {p : Submodule R M} (hp : p.FG) :
    (span S (f '' (p : Set M))).spanFinrank ≤ p.spanFinrank := by
  have h := lift_spanRank_span_image_le f p
  rw [(hp.span_image f).spanRank_eq_spanFinrank, hp.spanRank_eq_spanFinrank] at h
  simpa using h

/-- A target submodule is the target-scalar span of its comap image if, for each
of its elements, the scalars clearing that element into the image generate the unit
left ideal. No finite-generation or scalar-surjectivity hypothesis is required. -/
theorem span_image_comap_eq_of_one_mem_span_smul_mem_range (f : M →ₛₗ[σ] N)
    (p : Submodule S N)
    (hclear : ∀ n ∈ p, (1 : S) ∈ Ideal.span {a : S | ∃ m : M, f m = a • n}) :
    span S (f '' (p.comap f : Set M)) = p := by
  apply le_antisymm
  · refine span_le.mpr ?_
    rintro _ ⟨m, hm, rfl⟩
    exact mem_comap.mp hm
  · intro n hn
    refine (span S (f '' (p.comap f : Set M))).mem_of_span_top_of_smul_mem
      {a : S | ∃ m : M, f m = a • n} ((Ideal.eq_top_iff_one _).2 (hclear n hn)) n ?_
    intro a
    obtain ⟨m, hm⟩ := a.property
    apply subset_span
    refine ⟨m, ?_, hm⟩
    apply mem_comap.mpr
    rw [hm]
    exact p.smul_mem _ hn

/-- Finite generation ascends from a submodule's comap when, pointwise, its
clearing scalars generate the unit left ideal. The source and target semirings may be
noncommutative, and the scalar homomorphism need not be surjective. -/
theorem fg_of_fg_comap_of_one_mem_span_smul_mem_range (f : M →ₛₗ[σ] N)
    (p : Submodule S N) (hfg : (p.comap f).FG)
    (hclear : ∀ n ∈ p, (1 : S) ∈ Ideal.span {a : S | ∃ m : M, f m = a • n}) : p.FG := by
  rw [← span_image_comap_eq_of_one_mem_span_smul_mem_range f p hclear]
  exact hfg.span_image f

/-- A target submodule is finitely generated if its comap is finitely generated and
multiplying each of its elements by a scalar with a left inverse puts it in the image.
No surjectivity of the scalar homomorphism is required. -/
theorem fg_of_fg_comap_of_left_inv_smul_mem_range (f : M →ₛₗ[σ] N)
    (p : Submodule S N) (hfg : (p.comap f).FG)
    (hclear : ∀ n ∈ p, ∃ m : M, ∃ a b : S, b * a = 1 ∧ f m = a • n) : p.FG := by
  apply fg_of_fg_comap_of_one_mem_span_smul_mem_range f p hfg
  intro n hn
  obtain ⟨m, a, b, hba, hm⟩ := hclear n hn
  have ha : a ∈ Ideal.span {a : S | ∃ m : M, f m = a • n} :=
    Ideal.subset_span ⟨m, hm⟩
  simpa only [hba] using
    (Ideal.span {a : S | ∃ m : M, f m = a • n}).mul_mem_left b ha

/-- Unit clearing transfers finite generation from the comap of a target submodule.
The scalar homomorphism need not be surjective. -/
theorem fg_of_fg_comap_of_unit_smul_mem_range (f : M →ₛₗ[σ] N)
    (p : Submodule S N) (hfg : (p.comap f).FG)
    (hclear : ∀ n ∈ p, ∃ m : M, ∃ a : S, IsUnit a ∧ f m = a • n) : p.FG := by
  apply fg_of_fg_comap_of_left_inv_smul_mem_range f p hfg
  intro n hn
  obtain ⟨m, a, ha, hm⟩ := hclear n hn
  obtain ⟨b, hba⟩ := ha.exists_left_inv
  exact ⟨m, a, b, hba, hm⟩

end Submodule

namespace Module.Finite

variable {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN}
variable [Semiring R] [Semiring S] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module S N] {σ : R →+* S}

/-- Finite generation ascends along a semilinear map if every target element can be
multiplied into its image by a scalar with a left inverse. The scalar homomorphism
need not be surjective. -/
theorem of_left_inv_smul_mem_range (f : M →ₛₗ[σ] N) (hM : Module.Finite R M)
    (hclear : ∀ n : N, ∃ m : M, ∃ a b : S, b * a = 1 ∧ f m = a • n) :
    Module.Finite S N := by
  apply Module.finite_def.mpr
  apply Submodule.fg_of_fg_comap_of_left_inv_smul_mem_range f ⊤
  · simpa only [Submodule.comap_top] using Module.finite_def.mp hM
  · intro n _
    exact hclear n

/-- Finite generation ascends along a semilinear map if a unit multiple of every
target element lies in its image. No surjectivity of the scalar homomorphism is needed. -/
theorem of_unit_smul_mem_range (f : M →ₛₗ[σ] N) (hM : Module.Finite R M)
    (hclear : ∀ n : N, ∃ m : M, ∃ a : S, IsUnit a ∧ f m = a • n) :
    Module.Finite S N := by
  apply Module.finite_def.mpr
  apply Submodule.fg_of_fg_comap_of_unit_smul_mem_range f ⊤
  · simpa only [Submodule.comap_top] using Module.finite_def.mp hM
  · intro n _
    exact hclear n

end Module.Finite
