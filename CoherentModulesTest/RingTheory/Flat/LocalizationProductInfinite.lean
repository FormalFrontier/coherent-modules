/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Flat.Localization
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# An infinite product of principal localizations with proper generator span

Let `R = ℕ → ZMod 2`, and let `e i` be the vector supported at `i`, with value one
there. The canonical diagonal map from `R` to `Π i, Localization.Away (e i)` is
an isomorphism for the canonical `R`-action. Its inverse evaluates the `i`th
localization at the `i`th coordinate. In particular this product is faithfully
flat over `R`.

Nevertheless the `e i` span a proper ideal: every element of their span has
finite support. Thus the faithfully-flat-to-unit-span implication for finite
families of principal localizations does not extend to arbitrary families.
The corresponding infinite direct sum is not faithfully flat.

The coordinate maps are ring-homomorphism lifts of evaluation, not alternative
algebra structures on `ZMod 2`. Since `R` is itself a function ring, the stock
common-scalar structures `Pi.instSMul`, `Pi.module`, and `Pi.algebra` are selected
locally, rather than the different coordinatewise coefficient-ring structures.
All the diagonal, scalar-value, linear-equivalence, and faithful-flatness
statements below use these same common-`R` data. Scalar compatibility of the
inverse is proved explicitly. Faithful flatness is transported from the regular
module using Mathlib's `Module.FaithfullyFlat.self` and
`Module.FaithfullyFlat.of_linearEquiv`.
The direct-sum contrast uses CoherentModules' arbitrary-index theorem
`Module.FaithfullyFlat.directSum_away_iff`.
-/

@[expose] public section

open scoped DirectSum

noncomputable section

namespace CoherentModulesTest.Flat.LocalizationProductInfinite

/-- The concrete nontrivial coefficient ring. -/
abbrev K := ZMod 2

/-- The ring of sequences, with its pointwise commutative ring structure. -/
abbrev R := ℕ → K

/-- The coordinate idempotent supported at `i`. -/
def e (i : ℕ) : R := Pi.single i 1

/-- The canonical localization at the `i`th coordinate idempotent. -/
abbrev A (i : ℕ) := Localization.Away (e i)

/-- The product with the canonical common `R`-algebra and module structures. -/
abbrev Product := Π i : ℕ, A i

-- Since `R` is itself a function ring, also a different coordinatewise-scalar
-- Pi instance is available. Select the stock common-`R` structures explicitly.
/-- The common `R`-scalar action on `Product`, with
`(r • z) i = algebraMap R (A i) r * z i`. -/
local instance : SMul R Product := Pi.instSMul
/-- The product of the canonical `R`-modules `A i`, using the same scalar from `R`
in every localization factor. -/
local instance : Module R Product := Pi.module ℕ A R
/-- The product `R`-algebra structure, with structure map
`r ↦ fun i ↦ algebraMap R (A i) r`. -/
local instance : Algebra R Product := Pi.algebra ℕ A

@[simp]
theorem e_apply_self (i : ℕ) : e i i = 1 := by
  simp [e]

@[simp]
theorem e_apply_of_ne {i j : ℕ} (h : j ≠ i) : e i j = 0 := by
  simp [e, h]

/-- Each coordinate vector is idempotent in the sequence ring. -/
@[simp]
theorem e_mul_self (i : ℕ) : e i * e i = e i := by
  ext j
  by_cases h : j = i
  · subst j
    simp
  · simp [h]

/-- Distinct coordinate idempotents are orthogonal. -/
theorem e_mul_of_ne {i j : ℕ} (h : i ≠ j) : e i * e j = 0 := by
  ext k
  by_cases hk : k = i
  · subst k
    simp [h]
  · simp [hk]

/-- The defining idempotence predicate for the localization API. -/
theorem e_isIdempotent (i : ℕ) : IsIdempotentElem (e i) := e_mul_self i

/-- An idempotent which becomes a unit becomes one in its localization. -/
@[simp]
theorem algebraMap_e_self (i : ℕ) : algebraMap R (A i) (e i) = 1 := by
  apply (IsLocalization.Away.algebraMap_isUnit (S := A i) (e i)).mul_left_inj.mp
  simpa only [map_mul, one_mul] using
    congrArg (algebraMap R (A i)) (e_mul_self i)

/-- The canonical reciprocal of the idempotent is also one. -/
@[simp]
theorem invSelf_eq_one (i : ℕ) :
    IsLocalization.Away.invSelf (S := A i) (e i) = 1 := by
  simpa only [algebraMap_e_self, one_mul] using
    (IsLocalization.Away.mul_invSelf (S := A i) (e i))

/-- Evaluation at the `i`th coordinate extends to the localization because it
sends `e i` to one. -/
def evaluationLift (i : ℕ) : A i →+* K :=
  Localization.awayLift (Pi.evalRingHom (fun _ : ℕ ↦ K) i) (e i) (by
    change IsUnit (e i i)
    rw [e_apply_self]
    exact isUnit_one)

/-- The lift agrees with evaluation on the canonical source map. -/
@[simp]
theorem evaluationLift_algebraMap (i : ℕ) (r : R) :
    evaluationLift i (algebraMap R (A i) r) = r i := by
  exact IsLocalization.Away.lift_eq (S := A i)
    (g := Pi.evalRingHom (fun _ : ℕ ↦ K) i) (e i) (by
      change IsUnit (e i i)
      rw [e_apply_self]
      exact isUnit_one) r

/-- The lifted evaluation sends the localization reciprocal to one. -/
theorem evaluationLift_invSelf (i : ℕ) :
    evaluationLift i (IsLocalization.Away.invSelf (S := A i) (e i)) = 1 := by
  rw [invSelf_eq_one, map_one]

/-- Constants mapped into the canonical localization. -/
def constantToAway (i : ℕ) : K →+* A i :=
  (algebraMap R (A i)).comp (Pi.constRingHom ℕ K)

theorem constantToAway_apply (i : ℕ) (c : K) :
    constantToAway i c = algebraMap R (A i) (fun _ : ℕ ↦ c) := rfl

/-- Multiplication by `e i` discards every coordinate other than `i`. -/
theorem e_mul_sub_constant (i : ℕ) (r : R) :
    e i * (r - (Pi.constRingHom ℕ K) (r i)) = 0 := by
  ext j
  change e i j * (r j - r i) = 0
  by_cases h : j = i
  · subst j
    simp
  · rw [e_apply_of_ne h, zero_mul]

/-- In the `i`th localization every source element equals its constant
`i`th-coordinate value. The proof uses the annihilator identity in `R`. -/
theorem algebraMap_eq_constant (i : ℕ) (r : R) :
    algebraMap R (A i) r = constantToAway i (r i) := by
  have h := congrArg (algebraMap R (A i)) (e_mul_sub_constant i r)
  have hsub : algebraMap R (A i) r -
      algebraMap R (A i) ((Pi.constRingHom ℕ K) (r i)) = 0 := by
    simpa only [map_mul, map_sub, map_zero, algebraMap_e_self, one_mul] using h
  exact sub_eq_zero.mp hsub

/-- Other coordinate idempotents vanish in the `i`th localization. -/
@[simp]
theorem algebraMap_e_of_ne {i j : ℕ} (h : i ≠ j) :
    algebraMap R (A i) (e j) = 0 := by
  rw [algebraMap_eq_constant, e_apply_of_ne h, map_zero]

@[simp]
theorem evaluationLift_constantToAway (i : ℕ) (c : K) :
    evaluationLift i (constantToAway i c) = c := by
  change evaluationLift i (algebraMap R (A i) ((Pi.constRingHom ℕ K) c)) = c
  rw [evaluationLift_algebraMap]
  rfl

/-- Constants and lifted evaluation are inverse on the localization at `e i`. -/
@[simp]
theorem constantToAway_evaluationLift (i : ℕ) (z : A i) :
    constantToAway i (evaluationLift i z) = z := by
  obtain ⟨r, rfl⟩ :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem
      (S := A i) (e i) (e_isIdempotent i) z
  rw [evaluationLift_algebraMap]
  exact (algebraMap_eq_constant i r).symm

/-- Each canonical localization is nontrivial, as witnessed by lifted evaluation. -/
theorem away_nontrivial (i : ℕ) : Nontrivial (A i) :=
  (evaluationLift i).domain_nontrivial

/-- The canonical diagonal `R`-algebra map. -/
def diagonal : R →+* Product := algebraMap R Product

@[simp]
theorem diagonal_apply (r : R) (i : ℕ) :
    diagonal r i = algebraMap R (A i) r := rfl

/-- Coordinatewise lifted evaluation reconstructs a sequence. -/
def reconstruction : Product →+* R :=
  RingHom.pi fun i ↦ (evaluationLift i).comp (Pi.evalRingHom A i)

@[simp]
theorem reconstruction_apply (z : Product) (i : ℕ) :
    reconstruction z i = evaluationLift i (z i) := rfl

@[simp]
theorem reconstruction_diagonal (r : R) : reconstruction (diagonal r) = r := by
  ext i
  exact evaluationLift_algebraMap i r

@[simp]
theorem diagonal_reconstruction (z : Product) : diagonal (reconstruction z) = z := by
  ext i
  change algebraMap R (A i) (reconstruction z) = z i
  rw [algebraMap_eq_constant]
  exact constantToAway_evaluationLift i (z i)

/-- Scalar compatibility for the canonical common `R`-action, coordinate by
coordinate. The source coefficient is evaluated at the same coordinate. -/
theorem reconstruction_smul_apply (r : R) (z : Product) (i : ℕ) :
    reconstruction (r • z) i = r i * reconstruction z i := by
  change evaluationLift i (r • z i) = r i * evaluationLift i (z i)
  rw [Algebra.smul_def (R := R) (A := A i) r (z i), map_mul,
    evaluationLift_algebraMap]

/-- The product is isomorphic to the regular `R`-module, with the canonical
algebra map as inverse. -/
def regularModuleEquiv : Product ≃ₗ[R] R where
  toFun := reconstruction
  invFun := diagonal
  left_inv := diagonal_reconstruction
  right_inv := reconstruction_diagonal
  map_add' z w := reconstruction.map_add z w
  map_smul' r z := by
    ext i
    change reconstruction (r • z) i = r i * reconstruction z i
    exact reconstruction_smul_apply r z i

@[simp]
theorem regularModuleEquiv_apply (z : Product) (i : ℕ) :
    regularModuleEquiv z i = evaluationLift i (z i) := rfl

@[simp]
theorem regularModuleEquiv_symm_apply (r : R) :
    regularModuleEquiv.symm r = algebraMap R Product r := rfl

theorem regularModuleEquiv_symm_apply_coordinate (r : R) (i : ℕ) :
    regularModuleEquiv.symm r i = algebraMap R (A i) r := rfl

/-- The canonical diagonal sends a coordinate idempotent to a single supported
unit in the corresponding localization coordinate. -/
theorem diagonal_e (j : ℕ) : diagonal (e j) = Pi.single j (1 : A j) := by
  ext i
  by_cases h : i = j
  · subst i
    simp
  · simp [h]

/-- The supported unit in the product is nonzero. -/
theorem diagonal_e_ne_zero (j : ℕ) : diagonal (e j) ≠ 0 := by
  let : Nontrivial (A j) := away_nontrivial j
  intro h
  have hj := congrFun h j
  have hone : (1 : A j) = 0 := by
    simpa only [diagonal_apply, algebraMap_e_self, Pi.zero_apply] using hj
  exact one_ne_zero hone

/-- The tuple of the canonical localization reciprocals. -/
def reciprocalTuple : Product := fun i ↦ IsLocalization.Away.invSelf (S := A i) (e i)

theorem reciprocalTuple_apply (i : ℕ) :
    reciprocalTuple i = IsLocalization.Away.invSelf (S := A i) (e i) := rfl

@[simp]
theorem reciprocalTuple_eq_one : reciprocalTuple = 1 := by
  ext i
  exact invSelf_eq_one i

theorem reconstruction_reciprocalTuple : reconstruction reciprocalTuple = 1 := by
  rw [reciprocalTuple_eq_one, map_one]

/-- Acting by a coordinate idempotent on the reciprocal tuple produces the
corresponding supported unit, not a diagonal unit. -/
theorem e_smul_reciprocalTuple (j : ℕ) :
    e j • reciprocalTuple = Pi.single j (1 : A j) := by
  calc
    e j • reciprocalTuple = algebraMap R Product (e j) := by
      rw [reciprocalTuple_eq_one,
        Algebra.smul_def (R := R) (A := Product) (e j) (1 : Product), mul_one]
    _ = Pi.single j (1 : A j) := diagonal_e j

/-- The complement of `e i` annihilates the `i`th localization. -/
theorem complement_smul_away (i : ℕ) (z : A i) : (1 - e i) • z = 0 := by
  rw [Algebra.smul_def (R := R) (A := A i) (1 - e i) z, map_sub, map_one,
    algebraMap_e_self, sub_self, zero_mul]

/-- This infinite product is faithfully flat for its canonical common
`R`-action, by its explicit equivalence with the regular module. -/
theorem product_faithfullyFlat : Module.FaithfullyFlat R Product := by
  exact Module.FaithfullyFlat.of_linearEquiv R R regularModuleEquiv

/-- The ideal of sequences vanishing above some finite bound. On `ℕ` these
are exactly the finite-support sequences. -/
def finiteSupportIdeal : Ideal R where
  carrier := {r | ∃ N : ℕ, ∀ i, N ≤ i → r i = 0}
  zero_mem' := ⟨0, fun _ _ ↦ rfl⟩
  add_mem' := by
    rintro r s ⟨N, hN⟩ ⟨M, hM⟩
    refine ⟨max N M, fun i hi ↦ ?_⟩
    change r i + s i = 0
    rw [hN i (le_trans (le_max_left _ _) hi),
      hM i (le_trans (le_max_right _ _) hi), add_zero]
  smul_mem' := by
    rintro a r ⟨N, hN⟩
    refine ⟨N, fun i hi ↦ ?_⟩
    change a i * r i = 0
    rw [hN i hi, mul_zero]

/-- Membership in the finite-support ideal means vanishing above a finite bound. -/
@[simp]
theorem mem_finiteSupportIdeal_iff {r : R} :
    r ∈ finiteSupportIdeal ↔ ∃ N : ℕ, ∀ i, N ≤ i → r i = 0 := Iff.rfl

/-- Every coordinate idempotent has finite support. -/
theorem e_mem_finiteSupportIdeal (i : ℕ) : e i ∈ finiteSupportIdeal := by
  refine mem_finiteSupportIdeal_iff.mpr ⟨i + 1, fun j hj ↦ ?_⟩
  exact e_apply_of_ne (ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self i) hj))

/-- The generator span consists of finite-support sequences. -/
theorem span_e_le_finiteSupportIdeal :
    Ideal.span (Set.range e) ≤ finiteSupportIdeal := by
  apply Ideal.span_le.mpr
  rintro r ⟨i, rfl⟩
  exact e_mem_finiteSupportIdeal i

/-- The constant-one sequence cannot vanish above a finite bound. Nontriviality
here is that of the concrete coefficient ring `ZMod 2`. -/
theorem finiteSupportIdeal_ne_top : finiteSupportIdeal ≠ ⊤ := by
  intro h
  have hone : (1 : R) ∈ finiteSupportIdeal := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨N, hN⟩ := mem_finiteSupportIdeal_iff.mp hone
  have hzero : (1 : K) = 0 := hN N le_rfl
  exact one_ne_zero hzero

/-- Although the canonical infinite product is faithfully flat, its coordinate
idempotents do not span the unit ideal. -/
theorem span_e_ne_top : Ideal.span (Set.range e) ≠ ⊤ := by
  intro h
  have hle : (⊤ : Ideal R) ≤ finiteSupportIdeal := h ▸ span_e_le_finiteSupportIdeal
  exact finiteSupportIdeal_ne_top (top_unique hle)

/-- The infinite direct sum differs from the product: it is not faithfully flat. -/
theorem directSum_not_faithfullyFlat : ¬ Module.FaithfullyFlat R (⨁ i : ℕ, A i) := by
  intro h
  exact span_e_ne_top ((Module.FaithfullyFlat.directSum_away_iff R e).mp h)

end CoherentModulesTest.Flat.LocalizationProductInfinite
