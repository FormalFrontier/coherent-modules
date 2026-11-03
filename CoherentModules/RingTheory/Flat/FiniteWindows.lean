/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Algebra.Ring.Subring.Basic

/-!
# Flatness from finite subring windows

A ring map is flat, respectively faithfully flat, if every pair of finite subsets
of its source and target lies in subrings on which its canonical restriction has
that property. The subrings need not be finitely generated or form a directed
system, and no condition on transition maps is required.

The flatness proof places a finite relation in one window and transports the
trivial-relation witnesses back along the subring inclusions. For faithful
flatness, a finite expression for the identity in an extended proper ideal fits
in one window; contraction of extended ideals gives a contradiction there.

## References

The proofs use Mathlib's equational criterion for flatness, developed by Mitchell
Lee and Junyan Xu, and its faithfully-flat ideal contraction theorem, developed
by Christian Merten, Yi Song and Sihan Su. The equational criterion is recorded
in the Stacks Project, Tags 00HK and 058D.
-/

@[expose] public section

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring map is flat if any finite subsets of its source and target are
contained in subrings on which its canonical restriction is flat. -/
theorem Flat.of_finite_subring_windows (f : R →+* S)
    (hwin : ∀ (r : Finset R) (s : Finset S),
      ∃ (A : Subring R) (B : Subring S),
        (↑r : Set R) ⊆ A ∧ (↑s : Set S) ⊆ B ∧
        ∃ h : ∀ a ∈ A, f a ∈ B, (f.restrict A B h).Flat) :
    f.Flat := by
  classical
  let := f.toAlgebra
  have hfg (z : R) : algebraMap R S z = f z := rfl
  change Module.Flat R S
  apply Module.Flat.of_forall_isTrivialRelation
  intro l a x hx
  obtain ⟨A, B, hA, hB, h, hflat⟩ :=
    hwin (Finset.univ.image a) (Finset.univ.image x)
  let a' (i : Fin l) : A := ⟨a i, hA (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
  let x' (i : Fin l) : B := ⟨x i, hB (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)⟩
  let g := f.restrict A B h
  let := g.toAlgebra
  have hgg (z : A) : algebraMap A B z = g z := rfl
  have : Module.Flat A B := hflat
  have hrel : ∑ i, a' i • x' i = 0 := by
    apply Subtype.ext
    simpa [Algebra.smul_def, hfg, hgg, a', x', g] using hx
  obtain ⟨k, c, y, hxy, hc⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero hrel
  refine ⟨k, fun i j => (c i j : R), fun j => (y j : S), ?_, ?_⟩
  · intro i
    simpa [Algebra.smul_def, hfg, hgg, x', g] using congrArg B.subtype (hxy i)
  · intro j
    simpa [a'] using congrArg A.subtype (hc j)

/-- A ring map is faithfully flat if any finite subsets of its source and target
are contained in subrings on which its canonical restriction is faithfully flat.
No finite generation or compatibility between different windows is required. -/
theorem FaithfullyFlat.of_finite_subring_windows (f : R →+* S)
    (hwin : ∀ (r : Finset R) (s : Finset S),
      ∃ (A : Subring R) (B : Subring S),
        (↑r : Set R) ⊆ A ∧ (↑s : Set S) ⊆ B ∧
        ∃ h : ∀ a ∈ A, f a ∈ B, (f.restrict A B h).FaithfullyFlat) :
    f.FaithfullyFlat := by
  classical
  have hflat : f.Flat := Flat.of_finite_subring_windows f fun r s => by
    obtain ⟨A, B, hA, hB, h, hf⟩ := hwin r s
    exact ⟨A, B, hA, hB, h, hf.flat⟩
  let := f.toAlgebra
  have hfg (z : R) : algebraMap R S z = f z := rfl
  change Module.FaithfullyFlat R S
  apply (Module.FaithfullyFlat.iff_flat_and_proper_ideal R S).mpr
  refine ⟨hflat, ?_⟩
  intro I hI htop
  have h1 : (1 : S) ∈ I • (⊤ : Submodule R S) := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨c, hc, hc1⟩ :=
    (Submodule.mem_ideal_smul_span_iff_exists_sum I (_root_.id : S → S) (1 : S)).mp
      (by simpa only [Set.range_id, Submodule.span_univ] using h1)
  obtain ⟨A, B, hA, hB, h, hf⟩ := hwin (c.support.image c) c.support
  let g := f.restrict A B h
  let := g.toAlgebra
  have : Module.FaithfullyFlat A B := hf
  let J : Ideal A := I.comap A.subtype
  let a (i : c.support) : A :=
    ⟨c i, hA (Finset.mem_image.mpr ⟨i, i.2, rfl⟩)⟩
  let b (i : c.support) : B := ⟨i, hB i.2⟩
  have hsumS : ∑ i : c.support, f (c i) * (i : S) = 1 := by
    rw [Finset.sum_coe_sort c.support (fun i : S => f (c i) * i)]
    simpa [Finsupp.sum, Algebra.smul_def, hfg] using hc1
  have hsum : ∑ i : c.support, g (a i) * b i = 1 := by
    apply Subtype.ext
    simpa [a, b, g] using hsumS
  have hone : (1 : B) ∈ J.map g := by
    rw [← hsum]
    exact Submodule.sum_mem _ fun i _ =>
      (J.map g).mul_mem_right (b i) (Ideal.mem_map_of_mem g (hc i))
  have hcontract : (J.map g).comap g = J :=
    Ideal.comap_map_eq_self_of_faithfullyFlat J
  have hJone : (1 : A) ∈ J := by
    rw [← hcontract]
    change g 1 ∈ J.map g
    simpa only [map_one] using hone
  have hIone : (1 : R) ∈ I := hJone
  apply hI
  apply top_unique
  intro r _
  simpa only [mul_one] using I.mul_mem_left r hIone

end RingHom
