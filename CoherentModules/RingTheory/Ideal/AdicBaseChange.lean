/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.TensorProduct.Submodule
public import CoherentModules.RingTheory.Ideal.AdicCompatibility
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Descent of submodule adic cofinality

Both `Ideal.HasSubmoduleAdicCofinality` and
`Ideal.HasFiniteSubmoduleAdicCofinality` descend along faithfully flat algebras
of commutative rings, or when the algebra admits a linear map to the base ring
sending one to one. This linear map need not preserve multiplication. The
algebra need not be module-finite, and the ideal need not be finitely generated.

The pointwise descent calculation applies to arbitrary modules and submodules
over commutative semirings. It extends the source intersection into the
intersection of the extensions by monotonicity, then reflects the resulting
inclusion. No equality between base change and intersections is needed. The full
cofinality property imposes no finite-generation condition on the submodule;
the finite-submodule property uses finite generation only to obtain a finite
extended submodule.

## References

The proofs use Mathlib's submodule base-change order reflection for faithfully
flat algebras, the linear-retraction reflection lemmas in
`CoherentModules.LinearAlgebra.TensorProduct.Submodule`, finite-module base
change, and finiteness under surjective linear maps. The tensor product has its
canonical left-factor algebra action.
-/

@[expose] public section

universe uR uA uM

open scoped Pointwise TensorProduct

namespace Submodule

private theorem adic_cofinality_of_baseChange_of_orderReflection
    {R : Type uR} {A : Type uA} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {M : Type uM} [AddCommMonoid M] [Module R M]
    (hReflect : ∀ P Q : Submodule R M, P.baseChange A ≤ Q.baseChange A → P ≤ Q)
    (I : Ideal R) (N : Submodule R M)
    (h : ∀ n : ℕ, ∃ m : ℕ,
      N.baseChange A ⊓
          (((I.map (algebraMap R A)) ^ m) •
            (⊤ : Submodule A (A ⊗[R] M))) ≤
        ((I.map (algebraMap R A)) ^ n) • N.baseChange A) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N := by
  intro n
  obtain ⟨m, hm⟩ := h n
  refine ⟨m, hReflect _ _ ?_⟩
  calc
    (N ⊓ ((I ^ m) • (⊤ : Submodule R M))).baseChange A ≤
        N.baseChange A ⊓ ((I ^ m) • (⊤ : Submodule R M)).baseChange A :=
      le_inf (baseChange_mono A inf_le_left) (baseChange_mono A inf_le_right)
    _ = N.baseChange A ⊓
        (((I.map (algebraMap R A)) ^ m) •
          (⊤ : Submodule A (A ⊗[R] M))) := by
      rw [baseChange_smul, Ideal.map_pow, baseChange_top]
    _ ≤ ((I.map (algebraMap R A)) ^ n) • N.baseChange A := hm
    _ = ((I ^ n) • N).baseChange A := by
      rw [baseChange_smul, Ideal.map_pow]

/-- Pointwise adic cofinality on an extended submodule descends along a
faithfully flat algebra. Neither the ambient module nor its submodule need be
finitely generated, and the ring, algebra and module universes are independent. -/
theorem adic_cofinality_of_baseChange
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    [Algebra R A] [Module.FaithfullyFlat R A]
    {M : Type uM} [AddCommGroup M] [Module R M]
    (I : Ideal R) (N : Submodule R M)
    (h : ∀ n : ℕ, ∃ m : ℕ,
      N.baseChange A ⊓
          (((I.map (algebraMap R A)) ^ m) •
            (⊤ : Submodule A (A ⊗[R] M))) ≤
        ((I.map (algebraMap R A)) ^ n) • N.baseChange A) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N := by
  exact adic_cofinality_of_baseChange_of_orderReflection (A := A)
    (fun _ _ hPQ => (baseChange_le_iff (A := A)).mp hPQ) I N h

/-- Pointwise adic cofinality on an extended submodule descends if the scalar
algebra admits a linear map to the coefficient semiring sending one to one.
The map need not preserve multiplication. Neither the ambient semimodule nor
its submodule need be finitely generated, and all three universes are independent. -/
theorem adic_cofinality_of_baseChange_of_linearRetraction
    {R : Type uR} {A : Type uA} [CommSemiring R] [CommSemiring A]
    [Algebra R A] {M : Type uM} [AddCommMonoid M] [Module R M]
    (p : A →ₗ[R] R) (hp : p (1 : A) = 1)
    (I : Ideal R) (N : Submodule R M)
    (h : ∀ n : ℕ, ∃ m : ℕ,
      N.baseChange A ⊓
          (((I.map (algebraMap R A)) ^ m) •
            (⊤ : Submodule A (A ⊗[R] M))) ≤
        ((I.map (algebraMap R A)) ^ n) • N.baseChange A) :
    ∀ n : ℕ, ∃ m : ℕ,
      N ⊓ ((I ^ m) • (⊤ : Submodule R M)) ≤ (I ^ n) • N := by
  exact adic_cofinality_of_baseChange_of_orderReflection (A := A)
    (fun P Q hPQ => (baseChange_le_iff_of_linearRetraction p hp P Q).mp hPQ) I N h

end Submodule

namespace Ideal

/-- Submodule adic cofinality descends from the extended ideal along a
faithfully flat algebra of commutative rings. No module-finiteness of the algebra,
finite generation of the ideal or submodules, or finite presentation of the
ambient finite modules is required. -/
theorem HasSubmoduleAdicCofinality.of_map_of_faithfullyFlat
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    [Algebra R A] [Module.FaithfullyFlat R A]
    {I : Ideal R} (hI : (I.map (algebraMap R A)).HasSubmoduleAdicCofinality) :
    I.HasSubmoduleAdicCofinality := by
  refine (hasSubmoduleAdicCofinality_iff I).2 ?_
  intro M _ _ _ N
  exact Submodule.adic_cofinality_of_baseChange I N (hI.cofinal (N.baseChange A))

/-- Finite-submodule adic cofinality descends from the extended ideal along a
faithfully flat algebra of commutative rings. No module-finiteness of the algebra,
finite generation of the ideal, or finite presentation of the ambient finite
modules is required. -/
theorem HasFiniteSubmoduleAdicCofinality.of_map_of_faithfullyFlat
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
    [Algebra R A] [Module.FaithfullyFlat R A]
    {I : Ideal R} (hI : (I.map (algebraMap R A)).HasFiniteSubmoduleAdicCofinality) :
    I.HasFiniteSubmoduleAdicCofinality := by
  refine (hasFiniteSubmoduleAdicCofinality_iff I).2 ?_
  intro M _ _ _ N hN
  let : Module.Finite R N := Module.Finite.of_fg hN
  let : Module.Finite A (N.baseChange A) :=
    Module.Finite.of_surjective (N.toBaseChange A) (N.toBaseChange_surjective A)
  exact Submodule.adic_cofinality_of_baseChange I N
    (hI.cofinal (N.baseChange A) Submodule.FG.of_finite)

/-- Submodule adic cofinality descends from the extended ideal if the scalar
algebra admits a linear map to the base ring sending one to one. The map need
not preserve multiplication. No module-finiteness of the algebra, finite
generation of the ideal or submodules, or finite presentation of the ambient
finite modules is required. -/
theorem HasSubmoduleAdicCofinality.of_map_of_linearRetraction
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [Algebra R A]
    {I : Ideal R} (hJ : (I.map (algebraMap R A)).HasSubmoduleAdicCofinality)
    (p : A →ₗ[R] R) (hp : p (1 : A) = 1) :
    I.HasSubmoduleAdicCofinality := by
  refine (hasSubmoduleAdicCofinality_iff I).2 ?_
  intro M _ _ _ N
  exact Submodule.adic_cofinality_of_baseChange_of_linearRetraction p hp I N
    (hJ.cofinal (N.baseChange A))

/-- Finite-submodule adic cofinality descends from the extended ideal if the
scalar algebra admits a linear map to the base ring sending one to one. The map
need not preserve multiplication. No module-finiteness of the algebra, finite
generation of the ideal, or finite presentation of the ambient finite modules
is required. -/
theorem HasFiniteSubmoduleAdicCofinality.of_map_of_linearRetraction
    {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] [Algebra R A]
    {I : Ideal R} (hJ : (I.map (algebraMap R A)).HasFiniteSubmoduleAdicCofinality)
    (p : A →ₗ[R] R) (hp : p (1 : A) = 1) :
    I.HasFiniteSubmoduleAdicCofinality := by
  refine (hasFiniteSubmoduleAdicCofinality_iff I).2 ?_
  intro M _ _ _ N hN
  let : Module.Finite R N := Module.Finite.of_fg hN
  let : Module.Finite A (N.baseChange A) :=
    Module.Finite.of_surjective (N.toBaseChange A) (N.toBaseChange_surjective A)
  exact Submodule.adic_cofinality_of_baseChange_of_linearRetraction p hp I N
    (hJ.cofinal (N.baseChange A) Submodule.FG.of_finite)

end Ideal
