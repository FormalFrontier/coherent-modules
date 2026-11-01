/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Localization and colons by finitely generated ideals

Extension followed by contraction along a localization commutes with taking the colon
by a finitely generated ideal. Finite generation supplies a common denominator for a
finite set of generators; the colon-span identity then extends the condition to the
whole ideal.
-/

@[expose] public section

universe u v

namespace IsLocalization

/-- Extension followed by contraction along a localization commutes with taking the
colon by a finitely generated ideal. No finiteness assumption on the numerator ideal
or nonvanishing assumption on the denominators is required. -/
theorem comap_map_colon {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S]
    (T : Submonoid R) [Algebra R S] [IsLocalization T S]
    (I J : Ideal R) (hJ : Submodule.FG (J : Submodule R R)) :
    Ideal.comap (algebraMap R S) ((I.colon (J : Set R)).map (algebraMap R S)) =
      (Ideal.comap (algebraMap R S) (I.map (algebraMap R S))).colon (J : Set R) := by
  ext x
  constructor
  · intro hx
    rw [Ideal.mem_comap, algebraMap_mem_map_algebraMap_iff T S] at hx
    obtain ⟨t, ht, htx⟩ := hx
    rw [Submodule.mem_colon]
    intro y hy
    rw [smul_eq_mul, Ideal.mem_comap, algebraMap_mem_map_algebraMap_iff T S]
    refine ⟨t, ht, ?_⟩
    have h := (Submodule.mem_colon.mp htx) y hy
    rw [smul_eq_mul] at h
    convert h using 1; ac_rfl
  · intro hx
    obtain ⟨s, hs, hsJ⟩ := Submodule.fg_def.mp hJ
    rw [Ideal.submodule_span_eq] at hsJ
    rw [← hsJ, Ideal.colon_span] at hx ⊢
    simp only [Submodule.mem_colon, Ideal.mem_comap,
      algebraMap_mem_map_algebraMap_iff T S, smul_eq_mul] at hx ⊢
    -- Multiplying the witnesses for an insertion preserves all earlier witnesses.
    have common : ∀ (s : Set R), s.Finite →
        (∀ y ∈ s, ∃ t ∈ T, t * (x * y) ∈ I) →
          ∃ t ∈ T, ∀ y ∈ s, (t * x) * y ∈ I := by
      intro s hs
      induction s, hs using Set.Finite.induction_on with
      | empty =>
          intro _
          exact ⟨1, T.one_mem, fun y hy => False.elim hy⟩
      | @insert a s _ _ ih =>
          intro h
          obtain ⟨m, hm, hma⟩ := h a (Set.mem_insert a s)
          obtain ⟨t, ht, hts⟩ := ih (fun y hy => h y (Set.mem_insert_of_mem a hy))
          refine ⟨m * t, T.mul_mem hm ht, ?_⟩
          intro y hy
          rcases Set.mem_insert_iff.mp hy with rfl | hy
          · convert I.mul_mem_left t hma using 1; ac_rfl
          · convert I.mul_mem_left m (hts y hy) using 1; ac_rfl
    exact common s hs hx

end IsLocalization
