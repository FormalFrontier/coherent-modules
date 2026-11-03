/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Direct sums across a zero complement

An embedding of index types induces a linear equivalence of direct sums when every omitted
summand is subsingleton. The forward map is the coproduct map on the singleton inclusions;
the inverse is restriction along the embedding. The scalar, both index types, and the
summand family have independent universes.

The integer-indexed specialization retains the same summands and scalar action in
nonnegative degrees. Classical decisions are used internally for the stock singleton maps.
-/

@[expose] public section

universe uR uI uK uA

namespace DirectSum

attribute [local instance] Classical.propDecidable Classical.decEq

section General

variable {R : Type uR} [Semiring R]
variable {ι : Type uI} {κ : Type uK}
variable {A : κ → Type uA} [∀ k, AddCommMonoid (A k)] [∀ k, Module R (A k)]

private noncomputable def complementForward (e : ι ↪ κ) :
    (⨁ i, A (e i)) →ₗ[R] ⨁ k, A k :=
  toModule R ι (⨁ k, A k) (fun i ↦ lof R κ A (e i))

private noncomputable def complementRestriction (e : ι ↪ κ) :
    (⨁ k, A k) →ₗ[R] ⨁ i, A (e i) where
  toFun := DFinsupp.comapDomain e e.injective
  map_add' := DFinsupp.comapDomain_add e e.injective
  map_smul' := DFinsupp.comapDomain_smul e e.injective

private theorem complementForward_lof (e : ι ↪ κ) (i : ι) (a : A (e i)) :
    complementForward (R := R) e (lof R ι (fun i ↦ A (e i)) i a) =
      lof R κ A (e i) a := by
  simp [complementForward]

private theorem complementForward_apply_image (e : ι ↪ κ)
    (x : ⨁ i, A (e i)) (i : ι) : complementForward (R := R) e x (e i) = x i := by
  have h : (component R κ A (e i)).comp (complementForward (R := R) e) =
      component R ι (fun i ↦ A (e i)) i := by
    apply linearMap_ext
    intro j
    apply LinearMap.ext
    intro a
    by_cases hji : j = i
    · subst j
      simp [LinearMap.comp_apply, complementForward_lof]
    · have heji : e j ≠ e i := fun h ↦ hji (e.injective h)
      simp [LinearMap.comp_apply, complementForward_lof, component.of, hji, heji]
  exact congrArg (fun f ↦ f x) h

private theorem complementForward_apply_of_not_mem_range (e : ι ↪ κ)
    (x : ⨁ i, A (e i)) (k : κ) (hk : k ∉ Set.range e) :
    complementForward (R := R) e x k = 0 := by
  have h : (component R κ A k).comp (complementForward (R := R) e) = 0 := by
    apply linearMap_ext
    intro i
    apply LinearMap.ext
    intro a
    have hik : e i ≠ k := fun h ↦ hk ⟨i, h⟩
    simp [LinearMap.comp_apply, complementForward_lof, component.of, hik]
  exact congrArg (fun f ↦ f x) h

variable (R A)

/-- Extending a direct sum by subsingleton complementary summands is a linear equivalence.
Its forward map is the direct-sum universal map, and its inverse is coefficient restriction. -/
noncomputable def linearEquivOfSubsingletonComplement (e : ι ↪ κ)
    (hOff : ∀ k, k ∉ Set.range e → Subsingleton (A k)) :
    (⨁ i, A (e i)) ≃ₗ[R] ⨁ k, A k :=
  { toLinearMap := toModule R ι (⨁ k, A k) (fun i ↦ lof R κ A (e i))
    invFun := DFinsupp.comapDomain e e.injective
    left_inv := by
      intro x
      apply DFinsupp.ext
      intro i
      exact complementForward_apply_image e x i
    right_inv := by
      intro y
      apply DFinsupp.ext
      intro k
      by_cases hk : k ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hk
        exact complementForward_apply_image e (complementRestriction (R := R) e y) i
      · exact @Subsingleton.elim (A k) (hOff k hk) _ _ }

variable {R A}

/-- The forward linear map is exactly the coproduct map on the retained inclusions. -/
theorem linearEquivOfSubsingletonComplement_toLinearMap (e : ι ↪ κ)
    (hOff : ∀ k, k ∉ Set.range e → Subsingleton (A k)) :
    (linearEquivOfSubsingletonComplement R A e hOff).toLinearMap =
      toModule R ι (⨁ k, A k) (fun i ↦ lof R κ A (e i)) :=
  rfl

/-- The inverse is the finite-support restriction supplied by `DFinsupp.comapDomain`. -/
theorem linearEquivOfSubsingletonComplement_symm_apply_eq_comapDomain (e : ι ↪ κ)
    (hOff : ∀ k, k ∉ Set.range e → Subsingleton (A k)) (y : ⨁ k, A k) :
    (linearEquivOfSubsingletonComplement R A e hOff).symm y =
      DFinsupp.comapDomain e e.injective y :=
  rfl

/-- The inverse reads precisely the coefficients at the embedded indices. -/
@[simp]
theorem linearEquivOfSubsingletonComplement_symm_apply (e : ι ↪ κ)
    (hOff : ∀ k, k ∉ Set.range e → Subsingleton (A k)) (y : ⨁ k, A k) (i : ι) :
    (linearEquivOfSubsingletonComplement R A e hOff).symm y i = y (e i) :=
  DFinsupp.comapDomain_apply e e.injective y i

/-- The forward map leaves every retained coefficient unchanged. -/
@[simp]
theorem linearEquivOfSubsingletonComplement_apply_image (e : ι ↪ κ)
    (hOff : ∀ k, k ∉ Set.range e → Subsingleton (A k))
    (x : ⨁ i, A (e i)) (i : ι) :
    linearEquivOfSubsingletonComplement R A e hOff x (e i) = x i :=
  complementForward_apply_image e x i

/-- The forward map has zero coefficient outside the embedded indices. -/
theorem linearEquivOfSubsingletonComplement_apply_of_not_mem_range (e : ι ↪ κ)
    (hOff : ∀ k, k ∉ Set.range e → Subsingleton (A k))
    (x : ⨁ i, A (e i)) (k : κ) (hk : k ∉ Set.range e) :
    linearEquivOfSubsingletonComplement R A e hOff x k = 0 :=
  complementForward_apply_of_not_mem_range e x k hk

/-- A retained singleton is sent to the corresponding singleton of the full direct sum. -/
@[simp]
theorem linearEquivOfSubsingletonComplement_lof (e : ι ↪ κ)
    (hOff : ∀ k, k ∉ Set.range e → Subsingleton (A k)) (i : ι) (a : A (e i)) :
    linearEquivOfSubsingletonComplement R A e hOff
        (lof R ι (fun i ↦ A (e i)) i a) = lof R κ A (e i) a :=
  complementForward_lof e i a

/-- Restricting a singleton at an embedded index recovers the original singleton. -/
@[simp]
theorem linearEquivOfSubsingletonComplement_symm_lof (e : ι ↪ κ)
    (hOff : ∀ k, k ∉ Set.range e → Subsingleton (A k)) (i : ι) (a : A (e i)) :
    (linearEquivOfSubsingletonComplement R A e hOff).symm (lof R κ A (e i) a) =
      lof R ι (fun i ↦ A (e i)) i a := by
  rw [← linearEquivOfSubsingletonComplement_lof e hOff i a]
  exact (linearEquivOfSubsingletonComplement R A e hOff).symm_apply_apply _

/-- Restriction kills a singleton outside the embedded indices. -/
@[simp]
theorem linearEquivOfSubsingletonComplement_symm_lof_of_not_mem_range (e : ι ↪ κ)
    (hOff : ∀ k, k ∉ Set.range e → Subsingleton (A k))
    (k : κ) (hk : k ∉ Set.range e) (a : A k) :
    (linearEquivOfSubsingletonComplement R A e hOff).symm (lof R κ A k a) = 0 := by
  apply DFinsupp.ext
  intro i
  rw [linearEquivOfSubsingletonComplement_symm_apply]
  change DFinsupp.single k a (e i) = 0
  have hki : k ≠ e i := fun h ↦ hk ⟨i, h.symm⟩
  simp [DFinsupp.single_apply, hki]

/-- A singleton in a complementary summand is itself zero. -/
theorem linearEquivOfSubsingletonComplement_lof_eq_zero_of_not_mem_range (e : ι ↪ κ)
    (hOff : ∀ k, k ∉ Set.range e → Subsingleton (A k))
    (k : κ) (hk : k ∉ Set.range e) (a : A k) : lof R κ A k a = 0 := by
  apply (linearEquivOfSubsingletonComplement R A e hOff).symm.injective
  simpa using linearEquivOfSubsingletonComplement_symm_lof_of_not_mem_range e hOff k hk a

/-- The forward map is uniquely determined by its values on the singleton inclusions. -/
theorem linearEquivOfSubsingletonComplement_unique (e : ι ↪ κ)
    (hOff : ∀ k, k ∉ Set.range e → Subsingleton (A k))
    (f : (⨁ i, A (e i)) →ₗ[R] ⨁ k, A k)
    (hf : ∀ i a, f (lof R ι (fun i ↦ A (e i)) i a) = lof R κ A (e i) a) :
    f = (linearEquivOfSubsingletonComplement R A e hOff).toLinearMap := by
  apply linearMap_ext
  intro i
  apply LinearMap.ext
  intro a
  change f (lof R ι (fun i ↦ A (e i)) i a) =
    linearEquivOfSubsingletonComplement R A e hOff (lof R ι (fun i ↦ A (e i)) i a)
  rw [linearEquivOfSubsingletonComplement_lof]
  exact hf i a

/-- Coefficient restriction uniquely determines the inverse, even among arbitrary functions. -/
theorem linearEquivOfSubsingletonComplement_symm_unique (e : ι ↪ κ)
    (hOff : ∀ k, k ∉ Set.range e → Subsingleton (A k))
    (g : (⨁ k, A k) → ⨁ i, A (e i)) (hg : ∀ y i, g y i = y (e i)) :
    g = (linearEquivOfSubsingletonComplement R A e hOff).symm := by
  funext y
  apply DFinsupp.ext
  intro i
  exact (hg y i).trans (linearEquivOfSubsingletonComplement_symm_apply e hOff y i).symm

/-- For an equivalence of indices, restriction agrees with `DirectSum.lequivCongrLeft`. -/
theorem linearEquivOfSubsingletonComplement_symm_equiv (h : κ ≃ ι)
    (hOff : ∀ k, k ∉ Set.range h.symm.toEmbedding → Subsingleton (A k)) :
    (linearEquivOfSubsingletonComplement R A h.symm.toEmbedding hOff).symm =
      lequivCongrLeft R h := by
  apply LinearEquiv.ext
  intro y
  apply DFinsupp.ext
  intro i
  rw [linearEquivOfSubsingletonComplement_symm_apply, lequivCongrLeft_apply]
  rfl

/-- For an equivalence of indices, extension is the inverse of the stock reindexing. -/
theorem linearEquivOfSubsingletonComplement_equiv (h : κ ≃ ι)
    (hOff : ∀ k, k ∉ Set.range h.symm.toEmbedding → Subsingleton (A k)) :
    linearEquivOfSubsingletonComplement R A h.symm.toEmbedding hOff =
      (lequivCongrLeft R h).symm := by
  have hs := linearEquivOfSubsingletonComplement_symm_equiv (R := R) h hOff
  simpa only [LinearEquiv.symm_symm] using
    congrArg (fun f : (⨁ k, A k) ≃ₗ[R] (⨁ i, A (h.symm i)) ↦ f.symm) hs

end General

section Int

variable (R : Type uR) [Semiring R]
variable (A : ℤ → Type uA)

private theorem subsingleton_of_not_mem_natCast_range
    (hNeg : ∀ k, k < 0 → Subsingleton (A k))
    (k : ℤ) (hk : k ∉ Set.range (fun n : ℕ ↦ (n : ℤ))) : Subsingleton (A k) := by
  cases k with
  | ofNat n => exact (hk ⟨n, rfl⟩).elim
  | negSucc n => exact hNeg _ (Int.negSucc_lt_zero n)

variable [∀ k, AddCommMonoid (A k)] [∀ k, Module R (A k)]

/-- A family with subsingleton negative pieces has the same direct sum as its
natural-number restriction, with the original summands and scalar action. -/
noncomputable def linearEquivIntOfSubsingletonNeg
    (hNeg : ∀ k, k < 0 → Subsingleton (A k)) :
    (⨁ n : ℕ, A (n : ℤ)) ≃ₗ[R] ⨁ k : ℤ, A k :=
  linearEquivOfSubsingletonComplement R A
    (⟨fun n : ℕ ↦ (n : ℤ), Nat.cast_injective⟩ : ℕ ↪ ℤ)
    (by exact subsingleton_of_not_mem_natCast_range A hNeg)

variable {R A}

/-- The integer specialization preserves each nonnegative singleton. -/
@[simp]
theorem linearEquivIntOfSubsingletonNeg_lof
    (hNeg : ∀ k, k < 0 → Subsingleton (A k)) (n : ℕ) (a : A (n : ℤ)) :
    linearEquivIntOfSubsingletonNeg R A hNeg
        (lof R ℕ (fun n ↦ A (n : ℤ)) n a) = lof R ℤ A (n : ℤ) a := by
  convert linearEquivOfSubsingletonComplement_lof (R := R) (A := A)
    (⟨fun n : ℕ ↦ (n : ℤ), Nat.cast_injective⟩ : ℕ ↪ ℤ)
    (subsingleton_of_not_mem_natCast_range A hNeg) n a using 1
  · apply congrArg (linearEquivIntOfSubsingletonNeg R A hNeg)
    apply DFinsupp.ext
    intro i
    conv_lhs => rw [apply_eq_component R]
    conv_rhs => rw [apply_eq_component R]
    by_cases hi : n = i <;> simp [component.of, hi]
  · apply DFinsupp.ext
    intro k
    conv_lhs => rw [apply_eq_component R]
    conv_rhs => rw [apply_eq_component R]
    by_cases hk : (n : ℤ) = k <;> simp [component.of, hk]

/-- The inverse of the integer specialization reads the nonnegative coefficients. -/
@[simp]
theorem linearEquivIntOfSubsingletonNeg_symm_apply
    (hNeg : ∀ k, k < 0 → Subsingleton (A k)) (y : ⨁ k : ℤ, A k) (n : ℕ) :
    (linearEquivIntOfSubsingletonNeg R A hNeg).symm y n = y (n : ℤ) :=
  linearEquivOfSubsingletonComplement_symm_apply (R := R) (A := A)
    (⟨fun n : ℕ ↦ (n : ℤ), Nat.cast_injective⟩ : ℕ ↪ ℤ)
    (subsingleton_of_not_mem_natCast_range A hNeg) y n

/-- The integer specialization leaves each nonnegative coefficient unchanged. -/
@[simp]
theorem linearEquivIntOfSubsingletonNeg_apply_natCast
    (hNeg : ∀ k, k < 0 → Subsingleton (A k))
    (x : ⨁ n : ℕ, A (n : ℤ)) (n : ℕ) :
    linearEquivIntOfSubsingletonNeg R A hNeg x (n : ℤ) = x n :=
  linearEquivOfSubsingletonComplement_apply_image (R := R) (A := A)
    (⟨fun n : ℕ ↦ (n : ℤ), Nat.cast_injective⟩ : ℕ ↪ ℤ)
    (subsingleton_of_not_mem_natCast_range A hNeg) x n

private theorem neg_not_mem_natCast_range (k : ℤ) (hk : k < 0) :
    k ∉ Set.range (fun n : ℕ ↦ (n : ℤ)) := by
  rintro ⟨n, hn⟩
  have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
  exact (not_le_of_gt hk) (hn ▸ hn0)

/-- The integer specialization extends by zero in every negative degree. -/
theorem linearEquivIntOfSubsingletonNeg_apply_of_neg
    (hNeg : ∀ k, k < 0 → Subsingleton (A k))
    (x : ⨁ n : ℕ, A (n : ℤ)) (k : ℤ) (hk : k < 0) :
    linearEquivIntOfSubsingletonNeg R A hNeg x k = 0 :=
  linearEquivOfSubsingletonComplement_apply_of_not_mem_range
    (R := R) (A := A)
    (⟨fun n : ℕ ↦ (n : ℤ), Nat.cast_injective⟩ : ℕ ↪ ℤ)
    (subsingleton_of_not_mem_natCast_range A hNeg) x k (neg_not_mem_natCast_range k hk)

/-- The inverse of the integer specialization recovers a nonnegative singleton. -/
@[simp]
theorem linearEquivIntOfSubsingletonNeg_symm_lof
    (hNeg : ∀ k, k < 0 → Subsingleton (A k)) (n : ℕ) (a : A (n : ℤ)) :
    (linearEquivIntOfSubsingletonNeg R A hNeg).symm (lof R ℤ A (n : ℤ) a) =
      lof R ℕ (fun n ↦ A (n : ℤ)) n a := by
  rw [← linearEquivIntOfSubsingletonNeg_lof hNeg n a]
  exact (linearEquivIntOfSubsingletonNeg R A hNeg).symm_apply_apply _

/-- The inverse of the integer specialization kills a negative singleton. -/
@[simp]
theorem linearEquivIntOfSubsingletonNeg_symm_lof_of_neg
    (hNeg : ∀ k, k < 0 → Subsingleton (A k)) (k : ℤ) (hk : k < 0) (a : A k) :
    (linearEquivIntOfSubsingletonNeg R A hNeg).symm (lof R ℤ A k a) = 0 := by
  have ha : a = 0 := @Subsingleton.elim (A k) (hNeg k hk) _ _
  simp [ha]

end Int

end DirectSum

namespace Module.Finite

/-- A finitely generated direct sum has only finitely many nontrivial summands. -/
theorem finite_nontrivial_summands
    {ι : Type uI} {R : Type uR} {M : ι → Type uA} [Semiring R]
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [Module.Finite R (DirectSum ι M)] : Set.Finite {i | ¬ Subsingleton (M i)} := by
  classical
  have hcompact : IsCompactElement (⊤ : Submodule R (DirectSum ι M)) :=
    (Submodule.fg_iff_compact _).mp Module.Finite.fg_top
  obtain ⟨s, hs⟩ := hcompact.exists_finset_of_le_iSup
    (fun i ↦ LinearMap.range (DirectSum.lof R ι M i))
    (le_of_eq (DFinsupp.iSup_range_lsingle (R := R) (M := M)).symm)
  refine s.finite_toSet.subset ?_
  intro i hi
  by_contra his
  have hker : (⊤ : Submodule R (DirectSum ι M)) ≤
      LinearMap.ker (DirectSum.component R ι M i) :=
    hs.trans <| iSup₂_le fun j hj ↦
      LinearMap.range_le_ker_iff.mpr <|
        DFinsupp.lapply_comp_lsingle_of_ne i j (by
          intro hij
          subst j
          exact his hj)
  apply hi
  have hzero (m : M i) : m = 0 := by
    have hm := LinearMap.mem_ker.mp
      (hker (Submodule.mem_top : DirectSum.lof R ι M i m ∈ ⊤))
    simpa only [DirectSum.component.lof_self] using hm
  exact ⟨fun x y ↦ (hzero x).trans (hzero y).symm⟩

end Module.Finite
