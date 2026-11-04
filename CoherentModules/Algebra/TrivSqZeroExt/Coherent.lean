/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.TrivSqZeroExt.Finite
public import CoherentModules.Algebra.TrivSqZeroExt.Kernel
public import CoherentModules.FinitePresentation
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Coherent trivial square-zero extensions

A trivial square-zero extension of a left coherent ring by a bimodule that is finitely
presented on the left is left coherent. Conversely, coherence of the extension forces
finite generation of the coefficient module if scalar multiplication on one vector is
injective. These results retain the given compatible bimodule actions, without centrality.
Over an arbitrary division ring, the extension is left coherent exactly when its coefficient
bimodule is finitely generated on the left, including the zero module. The canonical field
case recovers the finite-dimensionality criterion.

## Main declarations

* `TrivSqZeroExt.isCoherentRing`: coherence from finite presentation over a coherent ring.
* `TrivSqZeroExt.finite_of_isCoherentRing_of_injective_smul`: finite generation from
  coherence and one vector with injective scalar multiplication.
* `TrivSqZeroExt.isCoherentRing_iff_finite_of_divisionRing`: the finite-generation criterion
  over a division ring, for the given compatible bimodule actions.
* `TrivSqZeroExt.isCoherentRing_iff_finite`: the finite-dimensionality criterion over a field.

## Implementation notes

Necessity identifies the kernel of right multiplication by `inr v` with the first
projection kernel as submodules of the regular left module. The second projection is a
surjective semilinear map to the original coefficient module. The canonical opposite-action
scope is opened only for the field criterion; it does not replace the given left action.

## References

The proofs build on this library's coherent-module kernel and scalar-restriction results
and its semilinear second-projection map, using Mathlib's trivial square-zero extension,
finite-image and finite-presentation formalizations. The sufficiency proof combines
coherence of products with scalar restriction; its regular-action tower argument is also
used in `CoherentModules.Algebra.TrivSqZeroExt.Noetherian`.
-/

@[expose] public section

universe uR uM

namespace TrivSqZeroExt

/-- A trivial square-zero extension by a bimodule finitely presented on the left is
left coherent. -/
theorem isCoherentRing
    {R : Type uR} {M : Type uM}
    [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M]
    [IsCoherentRing R] [Module.FinitePresentation R M] :
    IsCoherentRing (TrivSqZeroExt R M) := by
  let S := TrivSqZeroExt R M
  have : Module.IsCoherent R M := Module.FinitePresentation.isCoherent
  have : Module.IsCoherent R S := inferInstanceAs (Module.IsCoherent R (R × M))
  have : Module.Finite R S := inferInstance
  have : IsScalarTower R S S :=
    ⟨fun r x y => by
      change (r • x) * y = r • (x * y)
      rw [← inl_mul_eq_smul, ← inl_mul_eq_smul, mul_assoc]⟩
  exact ⟨Module.IsCoherent.of_restrictScalars R⟩

private theorem ker_toSpanSingleton_inr
    {R : Type uR} {M : Type uM}
    [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M]
    (v : M) (hv : Function.Injective (fun r : R ↦ r • v)) :
    LinearMap.ker
        (LinearMap.toSpanSingleton (TrivSqZeroExt R M) (TrivSqZeroExt R M) (inr v)) =
      (RingHom.ker (fstHom ℕ R M : TrivSqZeroExt R M →+* R) :
        Submodule (TrivSqZeroExt R M) (TrivSqZeroExt R M)) := by
  ext x
  rw [LinearMap.mem_ker, RingHom.mem_ker]
  change x * inr v = 0 ↔ x.fst = 0
  constructor
  · intro hx
    apply hv
    simpa using congrArg TrivSqZeroExt.snd hx
  · intro hx
    apply TrivSqZeroExt.ext
    · simp
    · simp [hx]

/-- If a trivial square-zero extension is left coherent and scalar multiplication on one
coefficient vector is injective, the coefficient module is finitely generated on the left.

The base ring may be noncommutative, and the given compatible right action need not be
central. Injectivity is required for a single vector, not merely faithfulness of the module. -/
theorem finite_of_isCoherentRing_of_injective_smul
    {R : Type uR} {M : Type uM}
    [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M]
    [IsCoherentRing (TrivSqZeroExt R M)]
    (v : M) (hv : Function.Injective (fun r : R ↦ r • v)) :
    Module.Finite R M := by
  let B := TrivSqZeroExt R M
  -- This is right multiplication by `inr v`, hence linear for the regular left action.
  let f : B →ₗ[B] B := LinearMap.toSpanSingleton B B (inr v)
  let _ : Module.IsCoherent B (LinearMap.ker f) := Module.IsCoherent.ker f
  let _ : Module.Finite B (RingHom.ker (fstHom ℕ R M : B →+* R)) := by
    rw [← ker_toSpanSingleton_inr v hv]
    infer_instance
  exact Module.Finite.of_surjective (kerFstHomSnd R M) (kerFstHomSnd_surjective R M)

/-- A trivial square-zero extension of an arbitrary division ring by a compatible bimodule
is left coherent exactly when the bimodule is finitely generated on the left.

Both module structures are the given ones, and their actions need not be central. The
coefficient module may be zero; its universe is independent of the division ring's.
The argument specializes `finite_of_isCoherentRing_of_injective_smul` and `isCoherentRing`,
using that a division ring is left Noetherian. -/
theorem isCoherentRing_iff_finite_of_divisionRing
    (D : Type uR) (M : Type uM)
    [DivisionRing D] [AddCommGroup M] [Module D M] [Module Dᵐᵒᵖ M]
    [SMulCommClass D Dᵐᵒᵖ M] :
    IsCoherentRing (TrivSqZeroExt D M) ↔ Module.Finite D M := by
  constructor
  · intro h
    let _ : IsCoherentRing (TrivSqZeroExt D M) := h
    rcases subsingleton_or_nontrivial M with hM | hM
    · let _ : Subsingleton M := hM
      infer_instance
    · let _ : Nontrivial M := hM
      obtain ⟨v, hv⟩ := exists_ne (0 : M)
      apply finite_of_isCoherentRing_of_injective_smul v
      intro a b hab
      dsimp only at hab
      by_contra hne
      have hz : (a - b) • v = 0 := by rw [sub_smul, hab, sub_self]
      apply hv
      calc
        v = (a - b)⁻¹ • ((a - b) • v) := by
          rw [← mul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hne), one_smul]
        _ = 0 := by rw [hz, smul_zero]
  · intro h
    let _ : Module.Finite D M := h
    let _ : Module.FinitePresentation D M := Module.finitePresentation_of_finite D M
    exact isCoherentRing

open scoped TrivSqZeroExt in
/-- The canonical trivial square-zero extension of a field by a vector space is coherent
exactly when the vector space is finitely generated, equivalently finite-dimensional.

The left action is the given one, and the opposite action is the canonical action induced
by commutativity. The vector space may be zero; its universe is independent of the field's. -/
theorem isCoherentRing_iff_finite
    {k : Type uR} {V : Type uM} [Field k] [AddCommGroup V] [Module k V] :
    IsCoherentRing (TrivSqZeroExt k V) ↔ Module.Finite k V := by
  exact isCoherentRing_iff_finite_of_divisionRing k V

end TrivSqZeroExt
