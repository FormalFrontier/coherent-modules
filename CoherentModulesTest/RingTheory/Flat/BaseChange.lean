/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.NormNum

/-!
# Kernels and faithful flatness under scalar extension

The maximal ideal `(2)` of the integers extends to the unit ideal of the rationals.
The universal characterization therefore rules out reflection of faithful flatness
on all flat integer modules, in every test universe. This uses the converse through
the library's public entry point, rather than assuming a scalar-flatness or
surjectivity criterion.

The kernel formula also proves that flat scalar extension preserves injectivity
when the tensor map is viewed as an `S`-algebra homomorphism.
Equality of underlying ring homomorphisms relates that consumer to the `R`-algebra
tensor map, without `S`-actions on the original algebras.

For the countably generated free abelian group, the arbitrary-module annihilator
formula evaluates an intersection of rationally extended ideals. An infinite
basis verifies that the original module is not finite, and the base-changed
basis computes its rational tensor annihilator independently.
-/

@[expose] public section

open scoped TensorProduct

universe w

namespace CoherentModulesTest.Flat.BaseChange

/-- Even though rational scalar extension is flat, it fails to reflect faithful
flatness on all flat integer modules in any test universe. -/
theorem integerRationalNotUniversalReflection :
    ¬ ∀ (M : Type w) [AddCommGroup M] [Module ℤ M],
    Module.Flat ℤ M →
      (Module.FaithfullyFlat ℤ M ↔ Module.FaithfullyFlat ℚ (ℚ ⊗[ℤ] M)) := by
  intro h
  have hmax :=
    (Algebra.map_maximal_ne_top_iff_forall_faithfullyFlat_baseChange
      (R := ℤ) (S := ℚ)).mpr h
  have hmap : (Ideal.span ({2} : Set ℤ)).map (algebraMap ℤ ℚ) = ⊤ := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
    norm_num
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact hmax (Ideal.span ({2} : Set ℤ)) (Int.ideal_span_isMaximal_of_prime 2) hmap

universe uR uS uA uB uM

/-- An injective algebra homomorphism remains injective after flat scalar extension,
including when the tensor map is viewed as an `S`-algebra homomorphism. -/
theorem tensorMap_injective_of_injective
    {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}
    [CommRing R] [CommRing S] [Ring A] [Ring B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Module.Flat R S]
    (f : A →ₐ[R] B) (hf : Function.Injective f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
  have hmap :
      (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom =
        (Algebra.TensorProduct.map (AlgHom.id R S) f).toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext
    · exact RingHom.ext fun _ => rfl
    · exact RingHom.ext fun _ => rfl
  apply (RingHom.injective_iff_ker_eq_bot
    (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom).mpr
  rw [hmap, AlgHom.toRingHom_eq_coe,
    ← AlgHom.ker_coe (Algebra.TensorProduct.map (AlgHom.id R S) f)]
  simpa only [(RingHom.injective_iff_ker_eq_bot f).mp hf, Ideal.map_bot] using
    (Algebra.TensorProduct.ker_map_id_left (S := S) f)

/-- The annihilator formula recovers the ring-coefficient specialization of finite
faithful-action preservation. The existing faithful theorem also handles semiring
coefficients and is not replaced by this argument. -/
theorem faithfulSMul_baseChange_of_annihilator
    (R : Type uR) (S : Type uS) (M : Type uM)
    [CommRing R] [Semiring S] [Algebra R S]
    [AddCommMonoid M] [Module R M]
    [Module.Finite R M] [FaithfulSMul R M] [Module.Flat R S] :
    FaithfulSMul S (S ⊗[R] M) := by
  let : Ring S := Algebra.semiringToRing R
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  apply (Module.annihilator_eq_bot (R := S) (M := S ⊗[R] M)).mp
  rw [Module.annihilator_tensorProduct_eq_map_of_finite_of_flat R S M,
    (Module.annihilator_eq_bot (R := R) (M := M)).mpr inferInstance, Ideal.map_bot]

/-- The intersection formula applies to a nonfinite free abelian group. Rational
scalar extension gives a faithful module, so the intersection of the extended
annihilators of its finitely generated subgroups is zero. -/
theorem rationalInfiniteFreeAnnihilator :
    ¬ Module.Finite ℤ (ℕ →₀ ℤ) ∧
      (⨅ N : {N : Submodule ℤ (ℕ →₀ ℤ) // N.FG},
        Ideal.map (algebraMap ℤ ℚ) (Module.annihilator ℤ N.1)) = ⊥ := by
  let : Module.Flat ℤ ℚ := IsLocalization.flat ℚ (nonZeroDivisors ℤ)
  let b : Module.Basis ℕ ℤ (ℕ →₀ ℤ) := Finsupp.basisSingleOne
  refine ⟨Module.not_finite_of_infinite_basis b, ?_⟩
  rw [← Module.annihilator_tensorProduct_eq_iInf_map_of_flat ℤ ℚ (ℕ →₀ ℤ),
    (b.baseChange ℚ).repr.annihilator_eq, Module.annihilator_finsupp]
  exact (Module.annihilator_eq_bot (R := ℚ) (M := ℚ)).mpr inferInstance

end CoherentModulesTest.Flat.BaseChange
