/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Finsupp.ToDFinsupp
public import Mathlib.Data.DFinsupp.Sigma
public import Mathlib.Algebra.Module.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Basic

/-!
# Finite indexed products of finitely supported functions

Finitely supported functions commute with finite dependent products. The degree type is
arbitrary, and the coordinate modules may have different scalar semirings. The comparison
is linear over the product semiring, acting through the given coordinate module structures.

The construction uses Mathlib's Finsupp–DFinsupp comparison, dependent currying and
finite-index function equivalence. Its coefficient lemmas describe both directions without
unfolding that composition.
-/

@[expose] public section

universe uκ uι uR uM

namespace Finsupp

variable {κ : Type uκ} {ι : Type uι}
variable (R : ι → Type uR) (M : ι → Type uM)
variable [Finite ι] [∀ i, Semiring (R i)]
variable [∀ i, AddCommMonoid (M i)] [∀ i, Module (R i) (M i)]

/-- Finitely supported functions into a finite dependent product, compared coordinatewise
with the product of finitely supported functions. Scalars act through the original modules
over the product semiring. Finiteness is required of the coordinate index, not the degree type. -/
noncomputable def piLinearEquiv :
    (κ →₀ (∀ i : ι, M i)) ≃ₗ[∀ i : ι, R i] (∀ i : ι, κ →₀ M i) := by
  classical
  exact
    letI : Fintype ι := Fintype.ofFinite ι
    let E : (Π₀ i : ι, M i) ≃ (∀ i : ι, M i) :=
      DFinsupp.equivFunOnFintype (ι := ι) (β := M)
    let coefficientZero :
        E.symm (0 : ∀ i : ι, M i) = (0 : Π₀ i : ι, M i) :=
      (show E.symm (0 : ∀ i : ι, M i) = (0 : Π₀ i : ι, M i) from by
        simpa only [DFinsupp.coe_zero] using
          (DFinsupp.equivFunOnFintype_symm_coe (0 : Π₀ i : ι, M i)))
    let eCoefficient :
        (κ →₀ (∀ i : ι, M i)) ≃ (κ →₀ (Π₀ i : ι, M i)) :=
      Finsupp.mapRange.equiv E.symm coefficientZero
    let eOuter :
        (κ →₀ (Π₀ i : ι, M i)) ≃ (Π₀ k : κ, Π₀ i : ι, M i) :=
      finsuppEquivDFinsupp (ι := κ) (M := Π₀ i : ι, M i)
    let eFlatten :
        (Π₀ k : κ, Π₀ i : ι, M i) ≃
          (Π₀ p : (Σ k : κ, ι), M p.2) :=
      (DFinsupp.sigmaCurryEquiv
        (ι := κ) (α := fun _ : κ => ι)
        (δ := fun (_ : κ) (i : ι) => M i)).symm
    let h : (Σ k : κ, ι) ≃ (Σ i : ι, κ) :=
      ((Equiv.sigmaEquivProd κ ι).trans (Equiv.prodComm κ ι)).trans
        (Equiv.sigmaEquivProd ι κ).symm
    let eReindex :
        (Π₀ p : (Σ k : κ, ι), M p.2) ≃
          (Π₀ p : (Σ i : ι, κ), M ((h.symm p).2)) :=
      DFinsupp.equivCongrLeft
        (β := fun p : (Σ k : κ, ι) => M p.2) h
    let eSwap :
        (Π₀ p : (Σ k : κ, ι), M p.2) ≃
          (Π₀ p : (Σ i : ι, κ), M p.1) :=
      (show (Π₀ p : (Σ k : κ, ι), M p.2) ≃
          (Π₀ p : (Σ i : ι, κ), M p.1) from eReindex)
    let eCurry :
        (Π₀ p : (Σ i : ι, κ), M p.1) ≃
          (Π₀ i : ι, Π₀ k : κ, M i) :=
      DFinsupp.sigmaCurryEquiv
        (ι := ι) (α := fun _ : ι => κ)
        (δ := fun (i : ι) (_ : κ) => M i)
    let eFiniteOuter :
        (Π₀ i : ι, Π₀ k : κ, M i) ≃
          (∀ i : ι, Π₀ k : κ, M i) :=
      DFinsupp.equivFunOnFintype
        (ι := ι) (β := fun i : ι => Π₀ k : κ, M i)
    let eCoordinates :
        (∀ i : ι, Π₀ k : κ, M i) ≃ (∀ i : ι, κ →₀ M i) :=
      Equiv.piCongrRight (fun i : ι =>
        (finsuppEquivDFinsupp (ι := κ) (M := M i)).symm)
    let eData :
        (κ →₀ (∀ i : ι, M i)) ≃ (∀ i : ι, κ →₀ M i) :=
      ((((((eCoefficient.trans eOuter).trans eFlatten).trans eSwap).trans
        eCurry).trans eFiniteOuter).trans eCoordinates)
    { toFun := fun (f : κ →₀ (∀ i : ι, M i)) => eData f
      invFun := fun (g : ∀ i : ι, κ →₀ M i) => eData.symm g
      left_inv := fun (f : κ →₀ (∀ i : ι, M i)) =>
        Equiv.symm_apply_apply eData f
      right_inv := fun (g : ∀ i : ι, κ →₀ M i) =>
        Equiv.apply_symm_apply eData g
      map_add' :=
        (show ∀ (f g : κ →₀ (∀ i : ι, M i)),
          eData (f + g) = eData f + eData g from by
          intro f g
          ext i k
          rfl)
      map_smul' :=
        (show ∀ (r : ∀ i : ι, R i) (f : κ →₀ (∀ i : ι, M i)),
          eData (r • f) = r • eData f from by
          intro r f
          ext i k
          rfl) }

/-- The finite-product comparison preserves each degree and coordinate coefficient. -/
@[simp] theorem piLinearEquiv_apply (f : κ →₀ (∀ i : ι, M i)) (i : ι) (k : κ) :
    (piLinearEquiv R M f i) k = (f k) i := by
  classical
  rfl

/-- The inverse comparison assembles the given coordinate coefficients. -/
@[simp] theorem piLinearEquiv_symm_apply (g : ∀ i : ι, κ →₀ M i) (k : κ) (i : ι) :
    ((piLinearEquiv R M).symm g k) i = (g i) k := by
  simpa only [piLinearEquiv_apply] using
    congrArg (fun z : ∀ i : ι, κ →₀ M i => (z i) k)
      ((piLinearEquiv R M).apply_symm_apply g)

/-- A single supported coefficient maps to the corresponding coordinate singles. -/
@[simp] theorem piLinearEquiv_single (k : κ) (m : ∀ i : ι, M i) (i : ι) :
    piLinearEquiv R M (single k m) i = single k (m i) := by
  classical
  ext l
  simp only [piLinearEquiv_apply, single_apply]
  split_ifs <;> rfl

/-- Coordinate singles at one degree assemble into a single product coefficient. -/
@[simp] theorem piLinearEquiv_symm_single (k : κ) (m : ∀ i : ι, M i) :
    (piLinearEquiv R M).symm (fun i => single k (m i)) = single k m := by
  classical
  ext l i
  simp only [piLinearEquiv_symm_apply, single_apply]
  split_ifs <;> rfl

/-- A product scalar acts on a supported coefficient by its corresponding coordinate.
The scalar family need not be constant, and the scalar semirings need not be commutative. -/
theorem piLinearEquiv_smul_single (r : ∀ i : ι, R i) (k : κ)
    (m : ∀ i : ι, M i) (i : ι) :
    piLinearEquiv R M (r • single k m) i = single k (r i • m i) := by
  simp only [Pi.smul_apply', piLinearEquiv_single, smul_single]

end Finsupp
