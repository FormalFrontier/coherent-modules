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
# Faithfully flat descent of submodule adic cofinality

Both `Ideal.HasSubmoduleAdicCofinality` and
`Ideal.HasFiniteSubmoduleAdicCofinality` descend along faithfully flat algebras
of commutative rings. The algebra need not be module-finite, and the ideal need
not be finitely generated.

The shared pointwise descent theorem applies to arbitrary modules and submodules.
It extends the source intersection into the intersection of the extensions by
monotonicity, then reflects the resulting inclusion. No equality between base
change and intersections is needed. The full cofinality provider imposes no
finite-generation condition on the submodule; the finite-submodule provider
uses finite generation only to obtain a finite extended submodule.

## References

The proofs use Mathlib's submodule base-change order reflection for faithfully
flat algebras, finite-module base change, and finiteness under surjective linear
maps. The tensor product has its canonical left-factor algebra action.
-/

@[expose] public section

universe uR uA uM

open scoped Pointwise TensorProduct

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A]
  [Algebra R A] [Module.FaithfullyFlat R A]

namespace Submodule

/-- Pointwise adic cofinality on an extended submodule descends along a
faithfully flat algebra. Neither the ambient module nor its submodule need be
finitely generated, and the ring, algebra and module universes are independent. -/
theorem adic_cofinality_of_baseChange
    {M : Type uM} [AddCommGroup M] [Module R M]
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
  refine ⟨m, (baseChange_le_iff (A := A)).mp ?_⟩
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

end Submodule

namespace Ideal

/-- Submodule adic cofinality descends from the extended ideal along a
faithfully flat algebra of commutative rings. No module-finiteness of the algebra,
finite generation of the ideal or submodules, or finite presentation of the
ambient finite modules is required. -/
theorem HasSubmoduleAdicCofinality.of_map_of_faithfullyFlat
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
    {I : Ideal R} (hI : (I.map (algebraMap R A)).HasFiniteSubmoduleAdicCofinality) :
    I.HasFiniteSubmoduleAdicCofinality := by
  refine (hasFiniteSubmoduleAdicCofinality_iff I).2 ?_
  intro M _ _ _ N hN
  let : Module.Finite R N := Module.Finite.of_fg hN
  let : Module.Finite A (N.baseChange A) :=
    Module.Finite.of_surjective (N.toBaseChange A) (N.toBaseChange_surjective A)
  exact Submodule.adic_cofinality_of_baseChange I N
    (hI.cofinal (N.baseChange A) Submodule.FG.of_finite)

end Ideal
