/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Flat.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Faithfully flat tensor-product examples

Countably indexed free abelian groups give faithfully flat factors and a
faithfully flat tensor product, with none of these modules finitely generated.
A scalar factor paired with an empty-index module shows that one faithfully
flat factor is insufficient.

The models use Mathlib's Finsupp bases, tensor-product bases, ideal criterion
for faithful flatness and transport along linear equivalences, independently
of the tensor-product criterion. Further examples apply both directions of
the criterion to these models. A module-level client uses annihilator preservation
to show that tensoring with a faithfully flat module preserves and reflects faithful
action of the coefficient ring, without finiteness of the other module.
-/

open scoped TensorProduct

namespace CoherentModulesTest.Flat.TensorProduct

universe v

private theorem integerInfiniteFinsuppFactors :
    Module.FaithfullyFlat ℤ (ℕ →₀ ℤ) ∧
      Module.FaithfullyFlat ℤ (ULift.{v} ℕ →₀ ℤ) ∧
      ¬ Module.Finite ℤ (ℕ →₀ ℤ) ∧
      ¬ Module.Finite ℤ (ULift.{v} ℕ →₀ ℤ) := by
  refine ⟨Module.FaithfullyFlat.finsupp ℤ ℕ,
    Module.FaithfullyFlat.finsupp ℤ (ULift.{v} ℕ), ?_, ?_⟩
  · exact Module.not_finite_of_infinite_basis
      (Finsupp.basisSingleOne : Module.Basis ℕ ℤ (ℕ →₀ ℤ))
  · exact Module.not_finite_of_infinite_basis
      (Finsupp.basisSingleOne : Module.Basis (ULift.{v} ℕ) ℤ (ULift.{v} ℕ →₀ ℤ))

private theorem integerInfiniteFinsuppTensor :
    Module.FaithfullyFlat ℤ ((ℕ →₀ ℤ) ⊗[ℤ] (ULift.{v} ℕ →₀ ℤ)) ∧
      ¬ Module.Finite ℤ ((ℕ →₀ ℤ) ⊗[ℤ] (ULift.{v} ℕ →₀ ℤ)) := by
  classical
  let b : Module.Basis ℕ ℤ (ℕ →₀ ℤ) := Finsupp.basisSingleOne
  let c : Module.Basis (ULift.{v} ℕ) ℤ (ULift.{v} ℕ →₀ ℤ) := Finsupp.basisSingleOne
  let : Module.FaithfullyFlat ℤ ((ℕ × ULift.{v} ℕ) →₀ ℤ) :=
    Module.FaithfullyFlat.finsupp ℤ (ℕ × ULift.{v} ℕ)
  exact ⟨Module.FaithfullyFlat.of_linearEquiv ℤ _ (b.tensorProduct c).repr,
    Module.not_finite_of_infinite_basis (b.tensorProduct c)⟩

private theorem integerEmptyFinsuppNotFaithfullyFlat :
    ¬ Module.FaithfullyFlat ℤ (Fin 0 →₀ ℤ) := by
  intro h
  have htop : (⊥ : Ideal ℤ) = ⊤ :=
    ((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top
      ℤ (Fin 0 →₀ ℤ)).mp h).2 ⊥ (Subsingleton.elim _ _)
  exact bot_ne_top htop

/-- A scalar module is faithfully flat, but its tensor product with an empty-index free
module is not faithfully flat. -/
public theorem integerScalarEmptyBoundary :
    Module.FaithfullyFlat ℤ ℤ ∧
      Module.Flat ℤ (Fin 0 →₀ ℤ) ∧
      Subsingleton (Fin 0 →₀ ℤ) ∧
      ¬ Module.FaithfullyFlat ℤ (Fin 0 →₀ ℤ) ∧
      ¬ Module.FaithfullyFlat ℤ (ℤ ⊗[ℤ] (Fin 0 →₀ ℤ)) := by
  refine ⟨Module.FaithfullyFlat.self ℤ,
    Module.Flat.finsupp (R := ℤ) (Fin 0), inferInstance,
    integerEmptyFinsuppNotFaithfullyFlat, ?_⟩
  intro h
  have htop : (⊥ : Ideal ℤ) = ⊤ :=
    ((Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top
      ℤ (ℤ ⊗[ℤ] (Fin 0 →₀ ℤ))).mp h).2 ⊥ (Subsingleton.elim _ _)
  exact bot_ne_top htop

/-- Both directions of the tensor-product criterion apply to countably generated free
abelian groups in independent universes; neither factor nor the tensor product is finite. -/
public theorem integerInfiniteFinsuppTensorCriterion :
    Module.FaithfullyFlat ℤ (ℕ →₀ ℤ) ∧
      Module.FaithfullyFlat ℤ (ULift.{v} ℕ →₀ ℤ) ∧
      Module.FaithfullyFlat ℤ ((ℕ →₀ ℤ) ⊗[ℤ] (ULift.{v} ℕ →₀ ℤ)) ∧
      ¬ Module.Finite ℤ (ℕ →₀ ℤ) ∧
      ¬ Module.Finite ℤ (ULift.{v} ℕ →₀ ℤ) ∧
      ¬ Module.Finite ℤ ((ℕ →₀ ℤ) ⊗[ℤ] (ULift.{v} ℕ →₀ ℤ)) := by
  have hFactors := integerInfiniteFinsuppFactors.{v}
  have hTensor := integerInfiniteFinsuppTensor.{v}
  have hRecovered := (Module.FaithfullyFlat.tensorProduct_iff
    ℤ (ℕ →₀ ℤ) (ULift.{v} ℕ →₀ ℤ)).mp hTensor.1
  have hConstructed := (Module.FaithfullyFlat.tensorProduct_iff
    ℤ (ℕ →₀ ℤ) (ULift.{v} ℕ →₀ ℤ)).mpr ⟨hFactors.1, hFactors.2.1⟩
  exact ⟨hRecovered.1, hRecovered.2, hConstructed,
    hFactors.2.2.1, hFactors.2.2.2, hTensor.2⟩

/-- The tensor-product criterion detects the empty-index boundary even though the
scalar factor is faithfully flat and the empty-index factor is flat. -/
public theorem integerScalarEmptyTensorNotFaithfullyFlat :
    ¬ Module.FaithfullyFlat ℤ (ℤ ⊗[ℤ] (Fin 0 →₀ ℤ)) := by
  intro h
  exact integerEmptyFinsuppNotFaithfullyFlat
    ((Module.FaithfullyFlat.tensorProduct_iff ℤ ℤ (Fin 0 →₀ ℤ)).mp h).2

universe uR uP uM

/-- Faithful action of the coefficient ring is preserved and reflected by tensoring
with a faithfully flat module, without finiteness or flatness of the other module.
This concerns the coefficient-ring action, not an action of a larger scalar algebra. -/
public theorem faithfulSMul_tensorProduct_iff
    (R : Type uR) (P : Type uP) (M : Type uM)
    [CommRing R] [AddCommGroup P] [AddCommMonoid M]
    [Module R P] [Module R M] [Module.FaithfullyFlat R P] :
    FaithfulSMul R (P ⊗[R] M) ↔ FaithfulSMul R M := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  rw [← Module.annihilator_eq_bot, ← Module.annihilator_eq_bot,
    Module.FaithfullyFlat.annihilator_tensorProduct_eq R P M]

end CoherentModulesTest.Flat.TensorProduct
