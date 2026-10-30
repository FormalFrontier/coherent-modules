/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.RingTheory.Nakayama

/-!
# Ideal action and annihilators of finite modules

An ideal acts with full image on a finitely generated submodule exactly when
it is comaximal with that submodule's annihilator. For a finite module, every
maximal ideal acts with proper image exactly when the annihilator is contained
in the Jacobson radical of the zero ideal.

Only the submodule must be finitely generated in the first result; the ambient
module and the acting ideal can be arbitrary. The second result needs neither
flatness nor faithful scalar action. Both include zero rings and zero modules.

## References

These results use Mathlib's determinant-trick and Nakayama formalizations by
Johan Commelin and Chris Hughes, together with its ideal-action, annihilator and
Jacobson-radical APIs. The mathematical reference is
[Stacks Project, Nakayama's lemma, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV).
-/

@[expose] public section

universe u v

namespace Submodule.FG

/-- An ideal acts with full image on a finitely generated submodule if and only if
it is comaximal with its annihilator. This is an annihilator formulation of
Nakayama's lemma ([Stacks, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV));
the ambient module need not be finite. -/
theorem ideal_smul_eq_self_iff_sup_annihilator_eq_top
    {R : Type u} {P : Type v} [CommRing R] [AddCommMonoid P] [Module R P]
    {N : Submodule R P} (hN : N.FG) (I : Ideal R) :
    I • N = N ↔ I ⊔ N.annihilator = ⊤ := by
  constructor
  · intro h
    let := Module.addCommMonoidToAddCommGroup R (M := P)
    obtain ⟨r, hr, hrN⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hN h.ge
    apply (Ideal.eq_top_iff_one _).mpr
    exact Submodule.mem_sup.mpr ⟨1 - r, by simpa only [neg_sub] using I.neg_mem hr,
      r, Submodule.mem_annihilator.mpr hrN, sub_add_cancel 1 r⟩
  · intro h
    calc
      I • N = (I ⊔ N.annihilator) • N := by
        rw [Submodule.sup_smul, Submodule.annihilator_smul, sup_bot_eq]
      _ = N := by rw [h, Submodule.top_smul]

end Submodule.FG

namespace Module

/-- For a finite module, every maximal ideal acts with proper image if and only if
the annihilator is contained in the Jacobson radical of the zero ideal.
This follows from the annihilator form of Nakayama's lemma
([Stacks, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)), without flatness
or faithful scalar action. -/
theorem forall_maximal_smul_top_ne_top_iff_annihilator_le_jacobson
    {R : Type u} {P : Type v} [CommRing R] [AddCommMonoid P] [Module R P]
    [Module.Finite R P] :
    (∀ m : Ideal R, m.IsMaximal → m • (⊤ : Submodule R P) ≠ ⊤) ↔
      Module.annihilator R P ≤ Ideal.jacobson (⊥ : Ideal R) := by
  constructor
  · intro hP
    apply le_sInf
    rintro m ⟨_, hm⟩
    have hsup : m ⊔ Module.annihilator R P ≠ ⊤ := by
      intro h
      apply hP m hm
      apply (Module.Finite.fg_top.ideal_smul_eq_self_iff_sup_annihilator_eq_top m).mpr
      simpa only [Submodule.annihilator_top] using h
    exact le_sup_right.trans_eq (hm.eq_of_le hsup le_sup_left).symm
  · intro hA m hm htop
    have hAnn : Module.annihilator R P ≤ m :=
      hA.trans (sInf_le ⟨bot_le, hm⟩)
    have hsup : m ⊔ Module.annihilator R P = ⊤ := by
      simpa only [Submodule.annihilator_top] using
        (Module.Finite.fg_top.ideal_smul_eq_self_iff_sup_annihilator_eq_top m).mp htop
    exact hm.ne_top ((sup_eq_left.mpr hAnn).symm.trans hsup)

end Module
