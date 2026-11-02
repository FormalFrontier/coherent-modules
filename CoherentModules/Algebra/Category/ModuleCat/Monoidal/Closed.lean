/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Kim Morrison, Jakob von Raumer, Robert A. Spencer, Junyan Xu,
  Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# Tensor–Hom adjunction for semimodules

For a commutative semiring, the category of semimodules is monoidal closed. Its internal Hom
is the semimodule of categorical morphisms, with postcomposition as its action on morphisms.
The Hom functor has an independent carrier universe; the closed structure uses the common
scalar and carrier universe of the monoidal structure.

The comparison with `ModuleCat` uses its existing equivalence with `SemimoduleCat`, the tensor
comparison of that monoidal functor, and the linear equivalences between categorical morphisms
and linear maps. In particular, no identification of the two types of categorical morphisms
or of the two choices of closed structure is needed.

## References

This generalizes the construction in Mathlib's `ModuleCat.Monoidal.Closed` by Kevin Buzzard,
Kim Morrison and Jakob von Raumer, using the semimodule packaging of Robert A. Spencer and
Junyan Xu and the tensor universal property formalized by Kenny Lau and Mario Carneiro.
The inverse, naturality, triangle and universal-property APIs are those of Mathlib's generic
monoidal closed categories and adjunctions.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory

namespace SemimoduleCat

variable {R : Type u} [CommSemiring R]

/-- The semimodule of morphisms out of `M`, functorial by postcomposition. -/
def homFunctor (M : SemimoduleCat.{v} R) : SemimoduleCat.{v} R ⥤ SemimoduleCat.{v} R where
  obj N := of R (M ⟶ N)
  map f := ofHom
    { toFun := fun g => g ≫ f
      map_add' := fun g h => by
        apply hom_ext
        ext m
        exact f.hom.map_add (g m) (h m)
      map_smul' := fun r g => by
        apply hom_ext
        ext m
        exact f.hom.map_smul r (g m) }
  map_id N := by
    ext g m
    rfl
  map_comp f g := by
    ext h m
    rfl

/-- The objects of the morphism functor are the existing wrapped morphism semimodules. -/
theorem homFunctor_obj (M N : SemimoduleCat.{v} R) :
    (homFunctor M).obj N = of R (M ⟶ N) := rfl

/-- The action of the morphism functor is postcomposition. -/
@[simp]
theorem homFunctor_map_apply {M N P : SemimoduleCat.{v} R} (f : N ⟶ P) (g : M ⟶ N) :
    (homFunctor M).map f g = g ≫ f := rfl

/-- The tensor universal property, with the first tensor factor as the Hom parameter. -/
def monoidalClosedHomEquiv (M N P : SemimoduleCat.{u} R) :
    ((tensorLeft M).obj N ⟶ P) ≃ (N ⟶ (homFunctor M).obj P) where
  toFun f := ofHom₂ <| LinearMap.compr₂ (TensorProduct.mk R N M) ((β_ N M).hom ≫ f).hom
  invFun f := (β_ M N).hom ≫ ofHom (TensorProduct.lift f.hom₂)
  left_inv f := by
    ext : 1
    apply TensorProduct.ext'
    solve_by_elim

/-- Tensoring on the left is left adjoint to the wrapped morphism functor. -/
def tensorLeftHomAdjunction (M : SemimoduleCat.{u} R) : tensorLeft M ⊣ homFunctor M :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun N P => monoidalClosedHomEquiv M N P
      homEquiv_naturality_left_symm := by
        intros
        ext : 1
        apply TensorProduct.ext'
        intro m n
        rfl
      homEquiv_naturality_right := by
        intros
        ext n
        rfl }

/-- The Hom equivalence of the adjunction is the tensor universal property. -/
theorem tensorLeftHomAdjunction_homEquiv (M N P : SemimoduleCat.{u} R) :
    (tensorLeftHomAdjunction M).homEquiv N P = monoidalClosedHomEquiv M N P :=
  by simp only [tensorLeftHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

instance instMonoidalClosed : MonoidalClosed (SemimoduleCat.{u} R) where
  closed M := { rightAdj := homFunctor M, adj := tensorLeftHomAdjunction M }

/-- The chosen internal Hom object is the semimodule of wrapped categorical morphisms. -/
theorem ihom_obj (M N : SemimoduleCat.{u} R) :
    (ihom M).obj N = of R (M ⟶ N) := rfl

/-- Internal Hom acts on morphisms by postcomposition. -/
@[simp]
theorem ihom_map_apply {M N P : SemimoduleCat.{u} R} (f : N ⟶ P) (g : M ⟶ N) :
    (ihom M).map f g = g ≫ f := rfl

/-- Currying evaluates on a pure tensor, in the order of its two tensor factors. -/
@[simp]
theorem monoidalClosed_curry {M N P : SemimoduleCat.{u} R} (f : M ⊗ N ⟶ P)
    (m : M) (n : N) :
    ((MonoidalClosed.curry f).hom n).hom m = f (m ⊗ₜ[R] n) := rfl

/-- Uncurrying evaluates a morphism-valued map on a pure tensor. -/
@[simp]
theorem monoidalClosed_uncurry {M N P : SemimoduleCat.{u} R}
    (f : N ⟶ M ⟶[SemimoduleCat.{u} R] P) (m : M) (n : N) :
    MonoidalClosed.uncurry f (m ⊗ₜ[R] n) = (f n).hom m := rfl

/-- Evaluation is the counit of the tensor–Hom adjunction. -/
@[simp]
theorem ihom_ev_app_apply (M P : SemimoduleCat.{u} R) (m : M) (h : M ⟶ P) :
    Hom.hom (A := M ⊗ (ihom M).obj P) (B := P) ((ihom.ev M).app P)
      (m ⊗ₜ[R] h) = h m := by
  rw [← MonoidalClosed.uncurry_id_eq_ev]
  exact monoidalClosed_uncurry _ _ _

/-- Coevaluation sends `n` to the map `m ↦ m ⊗ₜ n`. -/
@[simp]
theorem ihom_coev_app_apply (M N : SemimoduleCat.{u} R) (n : N) (m : M) :
    Hom.hom (A := M) (B := M ⊗ N)
      (Hom.hom (A := N) (B := (ihom M).obj (M ⊗ N)) ((ihom.coev M).app N) n) m =
        m ⊗ₜ[R] n := by
  rw [← MonoidalClosed.curry_id_eq_coev]
  exact monoidalClosed_curry _ _ _

/-- The parameter action of internal Hom is precomposition. -/
@[simp]
theorem monoidalClosed_pre_app_apply {M N : SemimoduleCat.{u} R}
    (P : SemimoduleCat.{u} R) (f : N ⟶ M) (g : M ⟶ P) :
    (MonoidalClosed.pre f).app P g = f ≫ g := rfl

end SemimoduleCat

namespace ModuleCat

variable {R : Type u} [CommRing R]

local notation "E" => CategoryTheory.Equivalence.functor (equivalenceSemimoduleCat (R := R))

/-- The wrapped-Hom comparison for the equivalence from modules to semimodules.
Its components are induced by the two Hom linear equivalences. -/
def ihomSemimoduleIso (M : ModuleCat.{u} R) :
    ihom M ⋙ E ≅ E ⋙ ihom ((E).obj M) :=
  NatIso.ofComponents
    (fun P =>
      ((homLinearEquiv (M := M) (N := P) (S := R)).trans
        (SemimoduleCat.homLinearEquiv
          (M := (E).obj M) (N := (E).obj P) (S := R)).symm).toModuleIsoₛ)
    (by
      intro P Q f
      ext h
      rfl)

/-- The forward wrapped-Hom comparison is the functor's action on morphisms. -/
@[simp]
theorem ihomSemimoduleIso_hom_app_apply (M P : ModuleCat.{u} R) (h : M ⟶ P) :
    SemimoduleCat.Hom.hom (A := (E).obj ((ihom M).obj P))
      (B := (ihom ((E).obj M)).obj ((E).obj P)) ((ihomSemimoduleIso M).hom.app P) h =
        (E).map h := rfl

/-- The inverse wrapped-Hom comparison returns the module morphism of a linear map. -/
@[simp]
theorem ihomSemimoduleIso_inv_app_apply (M P : ModuleCat.{u} R)
    (h : (E).obj M ⟶ (E).obj P) :
    SemimoduleCat.Hom.hom (A := (ihom ((E).obj M)).obj ((E).obj P))
      (B := (E).obj ((ihom M).obj P)) ((ihomSemimoduleIso M).inv.app P) h =
        ofHom (X := M) (Y := P) h.hom := rfl

/-- The existing monoidal comparison for tensoring has the identity underlying tensor map. -/
@[simp]
theorem equivalenceSemimoduleCat_commTensorLeft_hom_apply (M N : ModuleCat.{u} R)
    (x : ((E).obj M ⊗ (E).obj N : SemimoduleCat.{u} R)) :
    SemimoduleCat.Hom.hom (A := (E).obj M ⊗ (E).obj N) (B := (E).obj (M ⊗ N))
      ((Functor.Monoidal.commTensorLeft E M).hom.app N) x = x := rfl

/-- The tensor comparison is natural in both tensor factors. -/
theorem equivalenceSemimoduleCat_tensor_naturality {M M' N N' : ModuleCat.{u} R}
    (a : M ⟶ M') (t : N ⟶ N') :
    (Functor.Monoidal.commTensorLeft E M).hom.app N ≫ (E).map (a ⊗ₘ t) =
      ((E).map a ⊗ₘ (E).map t) ≫ (Functor.Monoidal.commTensorLeft E M').hom.app N' := by
  apply SemimoduleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

/-- The auxiliary module Hom equivalence is the currying operation of its chosen adjunction. -/
theorem monoidalClosedHomEquiv_apply_eq_curry {M N P : ModuleCat.{u} R}
    (f : M ⊗ N ⟶ P) :
    monoidalClosedHomEquiv M N P f = MonoidalClosed.curry f := rfl

/-- The module and semimodule tensor universal properties commute with the tensor and Hom
comparisons. This is an equality of transported categorical morphisms. -/
theorem equivalenceSemimoduleCat_monoidalClosedHomEquiv {M N P : ModuleCat.{u} R}
    (f : M ⊗ N ⟶ P) :
    SemimoduleCat.monoidalClosedHomEquiv ((E).obj M) ((E).obj N) ((E).obj P)
        ((Functor.Monoidal.commTensorLeft E M).hom.app N ≫ (E).map f) =
      (E).map (monoidalClosedHomEquiv M N P f) ≫ (ihomSemimoduleIso M).hom.app P := by
  ext n
  rfl

/-- Currying commutes with the module-to-semimodule equivalence and the chosen comparisons. -/
theorem equivalenceSemimoduleCat_curry {M N P : ModuleCat.{u} R} (f : M ⊗ N ⟶ P) :
    MonoidalClosed.curry ((Functor.Monoidal.commTensorLeft E M).hom.app N ≫ (E).map f) =
      (E).map (MonoidalClosed.curry f) ≫ (ihomSemimoduleIso M).hom.app P := by
  ext n
  rfl

-- Reduce the functor-composition object types in the transported internal Hom.
set_option backward.isDefEq.respectTransparency false in
/-- The inverse tensor–Hom square commutes on every morphism. -/
theorem equivalenceSemimoduleCat_uncurry {M N P : ModuleCat.{u} R}
    (g : N ⟶ (ihom M).obj P) :
    MonoidalClosed.uncurry (C := SemimoduleCat.{u} R)
        (A := (E).obj M) (Y := (E).obj N) (X := (E).obj P)
        ((E).map g ≫ (ihomSemimoduleIso M).hom.app P) =
      (Functor.Monoidal.commTensorLeft E M).hom.app N ≫
        (E).map (MonoidalClosed.uncurry (C := ModuleCat.{u} R)
          (A := M) (Y := N) (X := P) g) := by
  apply SemimoduleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

/-- The currying comparison is natural in both the remaining tensor factor and the target. -/
theorem equivalenceSemimoduleCat_curry_naturality {M N N' P P' : ModuleCat.{u} R}
    (t : N' ⟶ N) (f : M ⊗ N ⟶ P) (s : P ⟶ P') :
    MonoidalClosed.curry
        (((E).obj M ◁ (E).map t) ≫
          ((Functor.Monoidal.commTensorLeft E M).hom.app N ≫ (E).map f) ≫ (E).map s) =
      (E).map t ≫ (E).map (MonoidalClosed.curry f) ≫ (ihomSemimoduleIso M).hom.app P ≫
        (ihom ((E).obj M)).map ((E).map s) := by
  rw [MonoidalClosed.curry_natural_left, MonoidalClosed.curry_natural_right,
    equivalenceSemimoduleCat_curry]
  simp only [Category.assoc]

/-- The wrapped-Hom comparison also commutes with precomposition in the Hom parameter. -/
theorem ihomSemimoduleIso_pre {M M' : ModuleCat.{u} R} (a : M' ⟶ M)
    (P : ModuleCat.{u} R) :
    (E).map ((MonoidalClosed.pre a).app P) ≫ (ihomSemimoduleIso M').hom.app P =
      (ihomSemimoduleIso M).hom.app P ≫ (MonoidalClosed.pre ((E).map a)).app ((E).obj P) := by
  rw [monoidalClosed_pre_app]
  ext h
  rfl

/-- The chosen units commute with the tensor and wrapped-Hom comparisons. -/
theorem equivalenceSemimoduleCat_coev (M N : ModuleCat.{u} R) :
    (ihom.coev ((E).obj M)).app ((E).obj N) ≫
        (ihom ((E).obj M)).map ((Functor.Monoidal.commTensorLeft E M).hom.app N) =
      (E).map ((ihom.coev M).app N) ≫ (ihomSemimoduleIso M).hom.app (M ⊗ N) := by
  ext n
  rfl

/-- The chosen counits commute with the tensor and wrapped-Hom comparisons. -/
theorem equivalenceSemimoduleCat_ev (M P : ModuleCat.{u} R) :
    ((E).obj M ◁ (ihomSemimoduleIso M).hom.app P) ≫ (ihom.ev ((E).obj M)).app ((E).obj P) =
      (Functor.Monoidal.commTensorLeft E M).hom.app ((ihom M).obj P) ≫
        (E).map ((ihom.ev M).app P) := by
  apply SemimoduleCat.MonoidalCategory.tensor_ext
  intro m h
  rfl

/-- Under the equivalence, the module counit's linear-map formula is the semimodule counit. -/
theorem equivalenceSemimoduleCat_ev_formula (M P : ModuleCat.{u} R) :
    ((E).obj M ◁ (ihomSemimoduleIso M).hom.app P) ≫ (ihom.ev ((E).obj M)).app ((E).obj P) =
      (Functor.Monoidal.commTensorLeft E M).hom.app ((ihom M).obj P) ≫
        (E).map (ModuleCat.ofHom (TensorProduct.uncurry (.id R) M ((ihom M).obj P) P
          (LinearMap.lcomp _ _ homLinearEquiv.toLinearMap ∘ₗ LinearMap.id.flip))) := by
  rw [← ihom_ev_app]
  exact equivalenceSemimoduleCat_ev M P

/-- Under the equivalence, the module unit's bilinear-map formula is the semimodule unit. -/
theorem equivalenceSemimoduleCat_coev_formula (M N : ModuleCat.{u} R) :
    (ihom.coev ((E).obj M)).app ((E).obj N) ≫
        (ihom ((E).obj M)).map ((Functor.Monoidal.commTensorLeft E M).hom.app N) =
      (E).map (ModuleCat.ofHom₂ (TensorProduct.mk _ _ _).flip) ≫
        (ihomSemimoduleIso M).hom.app (M ⊗ N) := by
  ext n
  rfl

/-- Under the equivalence, the module precomposition formula gives the semimodule parameter map. -/
theorem ihomSemimoduleIso_pre_formula {M N : ModuleCat.{u} R} (P : ModuleCat.{u} R)
    (f : N ⟶ M) :
    (E).map (ofHom (homLinearEquiv.symm.toLinearMap ∘ₗ
        LinearMap.lcomp _ _ f.hom ∘ₗ homLinearEquiv.toLinearMap)) ≫
        (ihomSemimoduleIso N).hom.app P =
      (ihomSemimoduleIso M).hom.app P ≫ (MonoidalClosed.pre ((E).map f)).app ((E).obj P) := by
  rw [← monoidalClosed_pre_app]
  exact ihomSemimoduleIso_pre f P

end ModuleCat
