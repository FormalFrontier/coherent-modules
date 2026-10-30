/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Tensor detection of finite zero modules

Tensoring with an arbitrary module `P` detects zero objects among finitely generated
modules exactly when every maximal ideal acts on `P` with proper image. Neither
flatness nor finite generation of `P` is needed. This is zero-object detection,
not faithfulness on linear maps or reflection of isomorphisms.

A nonzero finite module has a simple quotient, hence a quotient isomorphic to
`R ⧸ m` for a maximal ideal `m`. Tensor preserves this surjection, and the resulting
fiber is `P ⧸ (m • ⊤)`. Conversely, these cyclic quotients test the maximal-ideal
condition. The universal characterization lifts them to `Type (max u w)`; the
single-module implication has no universe floor on the finite module.

## References

The proof uses Mathlib's finite-module/coatomic and simple-module developments by
Johan Commelin and Aaron Anderson, tensor right exactness by Antoine Chambert-Loir,
and the quotient–tensor equivalences by Antoine Chambert-Loir and Jujian Zhang.
On finite modules it generalizes the triviality criterion in the faithful-flatness
API by Judith Ludwig, Florent Schaffhauser, Yunzhou Xie and Jujian Zhang, dropping
the flatness assumption on the tensor factor.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module

/-- Tensoring with `P` detects the zero module among finite modules if every maximal
ideal acts on `P` with proper image. No flatness or finiteness of `P` is required. -/
theorem subsingleton_tensorProduct_iff_of_finite
    {R : Type u} {P : Type v} {M : Type w}
    [CommRing R] [AddCommMonoid P] [Module R P]
    [AddCommMonoid M] [Module R M] [Module.Finite R M]
    (hP : ∀ m : Ideal R, m.IsMaximal → m • (⊤ : Submodule R P) ≠ ⊤) :
    Subsingleton (P ⊗[R] M) ↔ Subsingleton M := by
  let := Module.addCommMonoidToAddCommGroup R (M := P)
  let := Module.addCommMonoidToAddCommGroup R (M := M)
  constructor
  · intro h
    have := h
    nontriviality M
    obtain ⟨L, hL⟩ := IsCoatomic.exists_coatom (Submodule R M)
    have hsimple : IsSimpleModule R (M ⧸ L) := isSimpleModule_iff_isCoatom.mpr hL
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
    have hquot : Subsingleton (P ⊗[R] (M ⧸ L)) :=
      (LinearMap.lTensor_surjective P L.mkQ_surjective).subsingleton
    have hfiber : Subsingleton (P ⊗[R] (R ⧸ m)) :=
      (e.lTensor P).toEquiv.subsingleton_congr.mp hquot
    have hzero : Subsingleton (P ⧸ (m • (⊤ : Submodule R P))) :=
      (TensorProduct.tensorQuotEquivQuotSMul P m).toEquiv.subsingleton_congr.mp hfiber
    exact False.elim (hP m hm (Submodule.Quotient.subsingleton_iff.mp hzero))
  · intro h
    have := h
    infer_instance

/-- Tensoring with `P` preserves and reflects zero objects among finite modules
exactly when every maximal ideal acts on `P` with proper image. The tensor factor
has an independent universe and need not be flat or finite. -/
theorem forall_maximal_smul_top_ne_top_iff_forall_finite_tensorProduct
    (R : Type u) (P : Type v) [CommRing R] [AddCommMonoid P] [Module R P] :
    (∀ m : Ideal R, m.IsMaximal → m • (⊤ : Submodule R P) ≠ ⊤) ↔
      ∀ (M : Type (max u w)) [AddCommMonoid M] [Module R M],
        Module.Finite R M → (Subsingleton M ↔ Subsingleton (P ⊗[R] M)) := by
  constructor
  · intro hP M _ _ hM
    exact (subsingleton_tensorProduct_iff_of_finite hP).symm
  · intro h m hm htop
    let := Module.addCommMonoidToAddCommGroup R (M := P)
    have hfiber : Subsingleton (P ⊗[R] (R ⧸ m)) :=
      (TensorProduct.tensorQuotEquivQuotSMul P m).toEquiv.subsingleton_congr.mpr
        (Submodule.Quotient.subsingleton_iff.mpr htop)
    let e : ULift.{w} (R ⧸ m) ≃ₗ[R] R ⧸ m := ULift.moduleEquiv
    have hlift : Subsingleton (P ⊗[R] ULift.{w} (R ⧸ m)) :=
      (e.lTensor P).toEquiv.subsingleton_congr.mpr hfiber
    have hzero : Subsingleton (ULift.{w} (R ⧸ m)) :=
      (h (ULift.{w} (R ⧸ m)) inferInstance).mpr hlift
    have : Subsingleton (R ⧸ m) :=
      e.toEquiv.subsingleton_congr.mp hzero
    have : Nontrivial (R ⧸ m) := Submodule.Quotient.nontrivial_iff.mpr hm.ne_top
    exact zero_ne_one (Subsingleton.elim (0 : R ⧸ m) 1)

end Module
