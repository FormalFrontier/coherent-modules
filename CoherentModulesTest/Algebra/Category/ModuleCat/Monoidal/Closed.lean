/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Tensoring with a finite based semimodule preserves limits

The chosen basis gives a natural comparison from tensoring to internal Hom.
Its components compose the basis coordinate equivalence, tensor congruence,
tensor symmetry, the finite-product tensor equivalence, basis extension, and
`SemimoduleCat.homLinearEquiv`. Intermediate function spaces remain unbundled.

The construction uses Mathlib's basis API (Johannes Hölzl, Mario Carneiro,
Alexander Bentkamp), tensor API (Kenny Lau, Mario Carneiro, Judith Ludwig,
Christian Merten), wrapped morphism API (Robert A. Spencer, Junyan Xu), and
monoidal, adjunction and limit-transport APIs and their credited contributors.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped TensorProduct

universe u w diagramMorph diagramObj

namespace CoherentModulesTest.MonoidalClosed

variable {R : Type u} [CommSemiring R]
variable {M : SemimoduleCat.{u} R} {ι : Type w} [Finite ι]

/- A specified finite basis identifies tensoring with internal Hom naturally in
its target. Thus tensoring with this semimodule preserves limits of any size. -/
example (b : Module.Basis ι R M) :
    PreservesLimitsOfSize.{diagramMorph, diagramObj} (tensorLeft M) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e (N : SemimoduleCat.{u} R) : M ⊗[R] N ≃ₗ[R] (M ⟶ N) :=
    TensorProduct.congr b.equivFun (LinearEquiv.refl R N) ≪≫ₗ
      TensorProduct.comm R (ι → R) N ≪≫ₗ
      TensorProduct.piScalarRight R R N ι ≪≫ₗ
      b.constr R ≪≫ₗ
      (SemimoduleCat.homLinearEquiv (M := M) (N := N) (S := R)).symm
  have e_tmul (N : SemimoduleCat.{u} R) (m : M) (n : N) (i : ι) :
      (e N (m ⊗ₜ[R] n)).hom (b i) = b.repr m i • n := by
    simp [e]
  have e_naturality {N P : SemimoduleCat.{u} R} (f : N ⟶ P) (m : M) (n : N) :
      e P (m ⊗ₜ[R] f n) = e N (m ⊗ₜ[R] n) ≫ f := by
    apply SemimoduleCat.hom_ext
    apply b.ext
    intro i
    simp [e_tmul]
  let E : tensorLeft M ≅ ihom M :=
    NatIso.ofComponents (fun N ↦ (e N).toModuleIsoₛ) (by
      intro N P f
      apply SemimoduleCat.MonoidalCategory.tensor_ext
      intro m n
      exact e_naturality f m n)
  let : PreservesLimitsOfSize.{diagramMorph, diagramObj} (ihom M) :=
    (ihom.adjunction M).rightAdjoint_preservesLimits
  exact preservesLimits_of_natIso E.symm

end CoherentModulesTest.MonoidalClosed
