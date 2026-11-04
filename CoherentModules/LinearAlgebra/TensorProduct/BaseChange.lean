/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Balanced base change with right-factor scalars

For a commutative semiring tower `C → A → B`, put `S = A ⊗[C] B` and let
`F : S →ₐ[C] B ⊗[C] B` be the tensor map induced by the original map `A → B`
and the identity of `B`. The equivalence `Algebra.TensorProduct.cancelBaseChangeRight`
upgrades Mathlib's base-change cancellation to an `S`-algebra equivalence. Its source
has the right-factor `S`-algebra structure, and its target has the algebra structure
obtained by restriction along `F`.

Thus the source action is `s • (b ⊗ s') = b ⊗ (s * s')`, and the target action is
`s • t = F(s) * t`. The restricting map is `F`, rather than the multiplication
map `S → B`. The underlying ring equivalence and function are those
of Mathlib's algebra and module cancellation equivalences, respectively.

Composing `Algebra.TensorProduct.commRight A S B` with this equivalence gives
`S ⊗[A] B ≃ₐ[S] B ⊗[C] B`; its underlying `S`-linear equivalence can be used for
scalar-extension arguments. No flatness or finiteness hypothesis is needed.

## References

This construction uses Mathlib's algebra tensor-product cancellation, tensor map,
and right-factor algebra structure.
-/

@[expose] public section

universe uC uA uB

open scoped TensorProduct

namespace Algebra.TensorProduct

variable (C : Type uC) (A : Type uA) (B : Type uB)
    [CommSemiring C] [CommSemiring A] [CommSemiring B]
    [Algebra C A] [Algebra C B] [Algebra A B] [IsScalarTower C A B]

/-- Base-change cancellation sends the right-factor coefficient inclusion to the
tensor map induced by the original map `A → B` and the identity of `B`. -/
@[simp]
theorem cancelBaseChange_one_tmul (s : A ⊗[C] B) :
    cancelBaseChange C A B B B ((1 : B) ⊗ₜ[A] s) =
      map (IsScalarTower.toAlgHom C A B) (AlgHom.id C B) s := by
  induction s using _root_.TensorProduct.inductionOn with
  | tmul a b => simp [Algebra.smul_def]
  | add s t hs ht => simp [TensorProduct.tmul_add, hs, ht]

/-- Base-change cancellation as an algebra equivalence over `A ⊗[C] B`.
The source uses the right tensor factor, while the target is restricted along
`(A → B) ⊗ id`, with the original compatible algebra structures. -/
def cancelBaseChangeRight :
    @AlgEquiv (A ⊗[C] B) (B ⊗[A] (A ⊗[C] B)) (B ⊗[C] B) _ _ _
      (rightAlgebra (R := A) (A := B) (B := A ⊗[C] B))
      (map (IsScalarTower.toAlgHom C A B) (AlgHom.id C B)).toRingHom.toAlgebra := by
  letI : Algebra (A ⊗[C] B) (B ⊗[A] (A ⊗[C] B)) :=
    rightAlgebra (R := A) (A := B) (B := A ⊗[C] B)
  letI : Algebra (A ⊗[C] B) (B ⊗[C] B) :=
    (map (IsScalarTower.toAlgHom C A B) (AlgHom.id C B)).toRingHom.toAlgebra
  exact
    { (cancelBaseChange C A B B B).toRingEquiv with
      commutes' := fun s => by
        change cancelBaseChange C A B B B ((1 : B) ⊗ₜ[A] s) =
          map (IsScalarTower.toAlgHom C A B) (AlgHom.id C B) s
        exact cancelBaseChange_one_tmul C A B s }

/-- The right-scalar refinement has the same underlying ring equivalence as
base-change cancellation. -/
theorem cancelBaseChangeRight_toRingEquiv :
    @AlgEquiv.toRingEquiv (A ⊗[C] B) (B ⊗[A] (A ⊗[C] B)) (B ⊗[C] B) _ _ _
      (rightAlgebra (R := A) (A := B) (B := A ⊗[C] B))
      (map (IsScalarTower.toAlgHom C A B) (AlgHom.id C B)).toRingHom.toAlgebra
      (cancelBaseChangeRight C A B) =
        (cancelBaseChange C A B B B).toRingEquiv := rfl

@[simp]
theorem cancelBaseChangeRight_tmul (b : B) (a : A) (b' : B) :
    cancelBaseChangeRight C A B (b ⊗ₜ[A] (a ⊗ₜ[C] b')) =
      (a • b) ⊗ₜ[C] b' :=
  cancelBaseChange_tmul C A B B B b a b'

/-- The right-scalar refinement has the same underlying function as module
base-change cancellation, with its original first-factor `B`-linearity. -/
theorem coe_cancelBaseChangeRight :
    (cancelBaseChangeRight C A B : B ⊗[A] (A ⊗[C] B) → B ⊗[C] B) =
      (_root_.TensorProduct.AlgebraTensorModule.cancelBaseChange C A B B B :
        B ⊗[A] (A ⊗[C] B) → B ⊗[C] B) := by
  funext x
  induction x using _root_.TensorProduct.inductionOn with
  | tmul b s =>
    induction s using _root_.TensorProduct.inductionOn with
    | tmul a b' =>
      simp only [cancelBaseChangeRight_tmul,
        _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
    | add s t hs ht => simp only [TensorProduct.tmul_add, map_add, hs, ht]
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp]
theorem cancelBaseChangeRight_symm_tmul (b b' : B) :
    (@AlgEquiv.symm (A ⊗[C] B) (B ⊗[A] (A ⊗[C] B)) (B ⊗[C] B) _ _ _
      (rightAlgebra (R := A) (A := B) (B := A ⊗[C] B))
      (map (IsScalarTower.toAlgHom C A B) (AlgHom.id C B)).toRingHom.toAlgebra
      (cancelBaseChangeRight C A B)) (b ⊗ₜ[C] b') =
        b ⊗ₜ[A] ((1 : A) ⊗ₜ[C] b') :=
  cancelBaseChange_symm_tmul C A B B B b b'

@[simp]
theorem cancelBaseChangeRight_one_tmul (s : A ⊗[C] B) :
    cancelBaseChangeRight C A B ((1 : B) ⊗ₜ[A] s) =
      map (IsScalarTower.toAlgHom C A B) (AlgHom.id C B) s :=
  cancelBaseChange_one_tmul C A B s

/-- Flipping the tensor factors and then cancelling gives the base-change
comparison with the coefficient algebra on the left. -/
theorem commRight_trans_cancelBaseChangeRight_tmul (a : A) (b' b : B) :
    (@AlgEquiv.trans (A ⊗[C] B) ((A ⊗[C] B) ⊗[A] B) (B ⊗[A] (A ⊗[C] B))
      (B ⊗[C] B) _ _ _ _ _
      (rightAlgebra (R := A) (A := B) (B := A ⊗[C] B))
      (map (IsScalarTower.toAlgHom C A B) (AlgHom.id C B)).toRingHom.toAlgebra
      (commRight A (A ⊗[C] B) B) (cancelBaseChangeRight C A B))
      ((a ⊗ₜ[C] b') ⊗ₜ[A] b) = (a • b) ⊗ₜ[C] b' := by
  simp

theorem commRight_trans_cancelBaseChangeRight_symm_tmul (b b' : B) :
    (@AlgEquiv.symm (A ⊗[C] B) ((A ⊗[C] B) ⊗[A] B) (B ⊗[C] B) _ _ _ _
      (map (IsScalarTower.toAlgHom C A B) (AlgHom.id C B)).toRingHom.toAlgebra
      (@AlgEquiv.trans (A ⊗[C] B) ((A ⊗[C] B) ⊗[A] B) (B ⊗[A] (A ⊗[C] B))
        (B ⊗[C] B) _ _ _ _ _
        (rightAlgebra (R := A) (A := B) (B := A ⊗[C] B))
        (map (IsScalarTower.toAlgHom C A B) (AlgHom.id C B)).toRingHom.toAlgebra
        (commRight A (A ⊗[C] B) B) (cancelBaseChangeRight C A B)))
      (b ⊗ₜ[C] b') = ((1 : A) ⊗ₜ[C] b') ⊗ₜ[A] b := by
  simp

end Algebra.TensorProduct
