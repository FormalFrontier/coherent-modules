/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Basic
public import CoherentModules.RingTheory.Finiteness.Pure
public import CoherentModules.LinearAlgebra.TensorProduct.Submodule
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Coherence descends along faithfully flat scalar extension

If the canonical scalar extension `S ⊗[R] M` is coherent over a faithfully flat
`R`-algebra `S`, the original module `M` is coherent over `R`. The base ring is
commutative, but the scalar algebra need not be. Applying this to the regular
module gives descent of ring coherence.

The proof combines finiteness and finite-presentation descent under injective
tensor units with flat submodule base change. The tensor-unit criterion and
base-change equivalences are reused from Mathlib; the module descent APIs are
reused from the pure-finiteness theory. Additive group structures are derived
inside proofs, retaining the supplied additive monoids and scalar actions.

## References

* Kazuhiro Fujiwara and Fumiharu Kato,
  [*Foundations of Rigid Geometry I*](https://arxiv.org/abs/1308.4734v5),
  arXiv:1308.4734v5 (2017-02-28), Chapter 0, Proposition 3.3.2(2)
  (printed p. 103): the descent direction for finitely generated modules over
  commutative rings and its ring-coherence consequence. Here finiteness of `M`
  is derived from coherence after scalar extension, and `S` may be noncommutative.
  No ascent or biconditional is asserted.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

private theorem tensorUnits_injective
    (R : Type u) (S : Type v)
    [CommRing R] [Ring S] [Algebra R S] [Module.FaithfullyFlat R S] :
    ∀ (X : Type (max u w)) [AddCommMonoid X] [Module R X],
      Function.Injective (TensorProduct.mk R S X 1) := by
  intro X _ _
  let _ : AddCommGroup X := Module.addCommMonoidToAddCommGroup R
  exact (injective_iff_map_eq_zero (TensorProduct.mk R S X 1)).2
    (fun x hx => (Module.FaithfullyFlat.one_tmul_eq_zero_iff
      (R := R) (M := X) (A := S) x).mp hx)

/-- Coherence descends from canonical scalar extension along a faithfully flat
algebra. The scalar algebra need not be commutative, and finiteness of the original
module is derived rather than assumed. This is the descent direction of
Fujiwara–Kato, Chapter 0, Proposition 3.3.2(2), with these generalizations. -/
theorem Module.IsCoherent.of_isCoherent_tensorProduct_of_faithfullyFlat
    (R : Type u) (S : Type v) (M : Type w)
    [CommRing R] [Ring S] [Algebra R S]
    [AddCommMonoid M] [Module R M]
    [Module.FaithfullyFlat R S]
    [Module.IsCoherent S (S ⊗[R] M)] :
    Module.IsCoherent R M := by
  have hunit :
      ∀ (X : Type (max u w)) [AddCommMonoid X] [Module R X],
        Function.Injective (TensorProduct.mk R S X 1) :=
    tensorUnits_injective.{u, v, w} R S
  refine
    { finite := Module.Finite.of_finite_tensorProduct_of_injective R M S hunit
      finitePresentation_submodule := ?_ }
  intro N hN
  let _ : Module.Finite R N := Module.Finite.of_fg hN
  let _ : Module.Finite S (S ⊗[R] N) := Module.Finite.base_change R S N
  let IN : Submodule S (S ⊗[R] M) := N.baseChange S
  have hIN : IN.FG := Submodule.fg_range (N.subtype.baseChange S)
  let _ : Module.FinitePresentation S IN :=
    Module.IsCoherent.finitePresentation_submodule IN hIN
  let eN : S ⊗[R] N ≃ₗ[S] IN := Submodule.toBaseChange.toLinearEquiv S N
  let _ : AddCommGroup IN := Module.addCommMonoidToAddCommGroup S
  let _ : AddCommGroup (S ⊗[R] N) := Module.addCommMonoidToAddCommGroup S
  let _ : Module.FinitePresentation S (S ⊗[R] N) :=
    Module.FinitePresentation.of_equiv (R := S) (M := IN) (N := S ⊗[R] N) eN.symm
  exact Module.FinitePresentation.of_finitePresentation_tensorProduct_of_injective R N S hunit

/-- A ring admitting a coherent faithfully flat algebra is coherent. The scalar
algebra is allowed to be noncommutative. -/
theorem IsCoherentRing.of_faithfullyFlat
    (R : Type u) (S : Type v)
    [CommRing R] [Ring S] [Algebra R S]
    [Module.FaithfullyFlat R S] [IsCoherentRing S] :
    IsCoherentRing R := by
  let eunit : S ⊗[R] R ≃ₗ[S] S := TensorProduct.AlgebraTensorModule.rid R S S
  let _ : Module.IsCoherent S (S ⊗[R] R) := Module.IsCoherent.of_equiv eunit.symm
  exact ⟨Module.IsCoherent.of_isCoherent_tensorProduct_of_faithfullyFlat R S R⟩
