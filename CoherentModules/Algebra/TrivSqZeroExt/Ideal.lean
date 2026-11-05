/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.TrivSqZeroExt.Kernel
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Order.WithBot

/-!
# Left ideals of a trivial square-zero extension

For a division semiring `D` and an additive commutative group `M` with commuting left and
right `D`-module structures, `TrivSqZeroExt.idealOrderIsoWithTop` identifies the left ideals
of `TrivSqZeroExt D M` with `WithTop (Submodule D M)`. A coefficient submodule corresponds
to the ideal of elements whose first coordinate is zero and whose second coordinate lies
in that submodule. The adjoined top corresponds to the whole extension, not to the
projection kernel.

The coefficient submodules use the given left action; they need not be stable under the
right action. In particular, neither commutativity of `D` nor centrality of the actions is
required. The additive group assumption on `M` is used only to lift units from `D`.

## References

The construction uses Mathlib's trivial square-zero extension, its unit criterion, and
the submodule order isomorphisms `Submodule.mapIic` and
`Submodule.orderIsoMapComapOfBijective`.
-/

@[expose] public section

universe u v

namespace TrivSqZeroExt

section DivisionSemiring

variable (D : Type u) (M : Type v) [DivisionSemiring D] [AddCommGroup M]
  [Module D M] [Module Dᵐᵒᵖ M] [SMulCommClass D Dᵐᵒᵖ M]

/-- Every proper left ideal of a trivial square-zero extension over a division semiring
is contained in the kernel of the first projection. -/
theorem le_ker_fstHom_of_ne_top {I : Ideal (TrivSqZeroExt D M)} (hI : I ≠ ⊤) :
    I ≤ RingHom.ker (fstHom ℕ D M : TrivSqZeroExt D M →+* D) := by
  intro x hx
  change x.fst = 0
  by_contra hfst
  exact hI (I.eq_top_of_isUnit_mem hx
    (isUnit_iff_isUnit_fst.mpr (IsUnit.mk0 x.fst hfst)))

/-- The left-ideal lattice of a trivial square-zero extension over a division semiring
is the coefficient-submodule lattice with a new top element.

A proper ideal is sent to its coefficient submodule. The inverse sends a coefficient
submodule `N` to the ideal of pairs with zero first coordinate and second coordinate in
`N`, and sends the adjoined top to the whole extension. -/
noncomputable def idealOrderIsoWithTop :
    Ideal (TrivSqZeroExt D M) ≃o WithTop (Submodule D M) := by
  classical
  let p : TrivSqZeroExt D M →+* D := fstHom ℕ D M
  let K := RingHom.ker p
  letI : RingHomSurjective p := ⟨fun d ↦ ⟨inl d, rfl⟩⟩
  let e : Set.Iic K ≃o Submodule D M :=
    (Submodule.mapIic K).symm.trans
      (Submodule.orderIsoMapComapOfBijective (kerFstHomSnd D M)
        (kerFstHomSnd_bijective D M))
  let B (I : Ideal (TrivSqZeroExt D M)) : Submodule D M :=
    Submodule.map (kerFstHomSnd D M) (Submodule.comap K.subtype I)
  let J (N : Submodule D M) : Ideal (TrivSqZeroExt D M) :=
    Submodule.map K.subtype (Submodule.comap (kerFstHomSnd D M) N)
  have hproper (I : Ideal (TrivSqZeroExt D M)) (hI : I ≠ ⊤) : I ≤ K :=
    le_ker_fstHom_of_ne_top D M hI
  have hcoeff (N : Submodule D M) : J N ≠ ⊤ :=
    ne_top_of_le_ne_top (RingHom.ker_ne_top p) (e.symm N).property
  refine
    { toFun := fun I ↦ if I = ⊤ then ⊤ else ↑(B I)
      invFun := WithTop.recTopCoe ⊤ J
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · intro I
    change WithTop.recTopCoe ⊤ J (if I = ⊤ then ⊤ else ↑(B I)) = I
    by_cases hI : I = ⊤
    · subst I
      rw [ite_eq_left rfl, WithTop.recTopCoe_top]
    · rw [ite_eq_right hI]
      exact congrArg Subtype.val (e.symm_apply_apply ⟨I, hproper I hI⟩)
  · intro N
    induction N using WithTop.recTopCoe with
    | top =>
      change (if (⊤ : Ideal (TrivSqZeroExt D M)) = ⊤ then
        (⊤ : WithTop (Submodule D M)) else ↑(B ⊤)) = ⊤
      exact ite_eq_left rfl
    | coe N =>
      change (if J N = ⊤ then ⊤ else ↑(B (J N))) = (N : WithTop (Submodule D M))
      rw [ite_eq_right (hcoeff N)]
      exact congrArg (fun P : Submodule D M ↦ (P : WithTop (Submodule D M)))
        (e.apply_symm_apply N)
  · intro I I'
    change (if I = ⊤ then (⊤ : WithTop (Submodule D M)) else ↑(B I)) ≤
      (if I' = ⊤ then ⊤ else ↑(B I')) ↔ I ≤ I'
    by_cases hI' : I' = ⊤
    · subst I'
      simp
    · by_cases hI : I = ⊤
      · subst I
        rw [ite_eq_left rfl, ite_eq_right hI']
        constructor
        · intro h
          exact (WithTop.not_top_le_coe (B I') h).elim
        · intro h
          exact (hI' (le_antisymm le_top h)).elim
      · rw [ite_eq_right hI, ite_eq_right hI', WithTop.coe_le_coe]
        exact e.le_iff_le (x := ⟨I, hproper I hI⟩) (y := ⟨I', hproper I' hI'⟩)

/-- The inverse classifier maps a coefficient submodule into the projection kernel
using the second projection and the kernel's subtype map. -/
theorem idealOrderIsoWithTop_symm_coe (N : Submodule D M) :
    (idealOrderIsoWithTop D M).symm (N : WithTop (Submodule D M)) =
      Submodule.map (RingHom.ker (fstHom ℕ D M : TrivSqZeroExt D M →+* D)).subtype
        (Submodule.comap (kerFstHomSnd D M) N) := rfl

/-- Membership in the ideal classified by a coefficient submodule is coordinatewise. -/
@[simp] theorem mem_idealOrderIsoWithTop_symm_coe (N : Submodule D M)
    (x : TrivSqZeroExt D M) :
    x ∈ (idealOrderIsoWithTop D M).symm (N : WithTop (Submodule D M)) ↔
      x.fst = 0 ∧ x.snd ∈ N := by
  rw [idealOrderIsoWithTop_symm_coe, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨x, hx⟩, hy, rfl⟩

/-- The internal top coefficient submodule corresponds to the projection kernel,
not to the whole extension. -/
@[simp] theorem idealOrderIsoWithTop_symm_coe_top :
    (idealOrderIsoWithTop D M).symm (↑(⊤ : Submodule D M)) =
      RingHom.ker (fstHom ℕ D M : TrivSqZeroExt D M →+* D) := by
  ext x
  rw [mem_idealOrderIsoWithTop_symm_coe]
  change (x.fst = 0 ∧ x.snd ∈ (⊤ : Submodule D M)) ↔ x.fst = 0
  exact ⟨And.left, fun hx ↦ ⟨hx, Submodule.mem_top⟩⟩

/-- The projection kernel is sent to the internal top coefficient submodule. -/
@[simp] theorem idealOrderIsoWithTop_apply_ker :
    idealOrderIsoWithTop D M
        (RingHom.ker (fstHom ℕ D M : TrivSqZeroExt D M →+* D)) =
      (↑(⊤ : Submodule D M) : WithTop (Submodule D M)) := by
  rw [← idealOrderIsoWithTop_symm_coe_top D M, OrderIso.apply_symm_apply]

/-- The value of the classifier at a given coefficient submodule characterizes all
members of the original ideal without unfolding the classifier. -/
theorem idealOrderIsoWithTop_apply_eq_coe_iff (I : Ideal (TrivSqZeroExt D M))
    (N : Submodule D M) :
    idealOrderIsoWithTop D M I = (N : WithTop (Submodule D M)) ↔
      ∀ x : TrivSqZeroExt D M, x ∈ I ↔ x.fst = 0 ∧ x.snd ∈ N := by
  rw [← (idealOrderIsoWithTop D M).eq_symm_apply]
  constructor
  · intro h x
    rw [h, mem_idealOrderIsoWithTop_symm_coe]
  · intro h
    exact Submodule.ext fun x ↦ (h x).trans (mem_idealOrderIsoWithTop_symm_coe D M N x).symm

end DivisionSemiring

end TrivSqZeroExt
