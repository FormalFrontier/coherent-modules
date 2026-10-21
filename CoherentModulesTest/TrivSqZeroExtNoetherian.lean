/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Algebra.TrivSqZeroExt.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Module.PUnit
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Noetherianity criteria for trivial square-zero extensions

Applications of the criteria for associative rings and bimodules, together with
examples over zero rings, integer modules, matrix rings, and different universes.
The additional projection-kernel propositions are type-level checks for semirings.
-/

@[expose] public section

noncomputable section

namespace CoherentModulesTest.TrivSqZeroExtNoetherian

universe uR uM

section Ring

variable (R : Type uR) (M : Type uM)
  [Ring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]

example :
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  IsNoetherianRing (TrivSqZeroExt R M) ↔ IsNoetherianRing R ∧ Module.Finite R M :=
  TrivSqZeroExt.isNoetherianRing_iff

example :
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R
  IsNoetherianRing (TrivSqZeroExt R M) ↔ IsNoetherianRing R ∧ IsNoetherian R M :=
  TrivSqZeroExt.isNoetherianRing_iff_isNoetherian

end Ring

section Semiring

variable (R : Type uR) (M : Type uM)
  [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
  [SMulCommClass R Rᵐᵒᵖ M]

example : Prop :=
  IsNoetherian (TrivSqZeroExt R M)
    (RingHom.ker ((TrivSqZeroExt.fstHom ℕ R M).toRingHom)) ↔ IsNoetherian R M

end Semiring

section ZeroRing

open scoped TrivSqZeroExt

example : Ring (ZMod 1) := inferInstance
example : AddCommMonoid (PUnit : Type 0) := inferInstance
example : Module (ZMod 1) (PUnit : Type 0) := inferInstance
example : Module (ZMod 1)ᵐᵒᵖ (PUnit : Type 0) := inferInstance
example : SMulCommClass (ZMod 1) (ZMod 1)ᵐᵒᵖ (PUnit : Type 0) := inferInstance

example :
  IsNoetherianRing (TrivSqZeroExt (ZMod 1) (PUnit : Type 0)) ↔
    IsNoetherianRing (ZMod 1) ∧ Module.Finite (ZMod 1) (PUnit : Type 0) :=
  TrivSqZeroExt.isNoetherianRing_iff

example :
  IsNoetherianRing (TrivSqZeroExt (ZMod 1) (PUnit : Type 0)) ↔
    IsNoetherianRing (ZMod 1) ∧ IsNoetherian (ZMod 1) (PUnit : Type 0) :=
  TrivSqZeroExt.isNoetherianRing_iff_isNoetherian

example : Prop :=
  IsNoetherian (TrivSqZeroExt (ZMod 1) (PUnit : Type 0))
    (RingHom.ker ((TrivSqZeroExt.fstHom ℕ (ZMod 1) (PUnit : Type 0)).toRingHom)) ↔
      IsNoetherian (ZMod 1) (PUnit : Type 0)

end ZeroRing

section ZeroModule

open scoped TrivSqZeroExt

example : Ring (ℤ) := inferInstance
example : AddCommMonoid (PUnit : Type 0) := inferInstance
example : Module (ℤ) (PUnit : Type 0) := inferInstance
example : Module (ℤ)ᵐᵒᵖ (PUnit : Type 0) := inferInstance
example : SMulCommClass (ℤ) (ℤ)ᵐᵒᵖ (PUnit : Type 0) := inferInstance

example :
  IsNoetherianRing (TrivSqZeroExt (ℤ) (PUnit : Type 0)) ↔
    IsNoetherianRing (ℤ) ∧ Module.Finite (ℤ) (PUnit : Type 0) :=
  TrivSqZeroExt.isNoetherianRing_iff

example :
  IsNoetherianRing (TrivSqZeroExt (ℤ) (PUnit : Type 0)) ↔
    IsNoetherianRing (ℤ) ∧ IsNoetherian (ℤ) (PUnit : Type 0) :=
  TrivSqZeroExt.isNoetherianRing_iff_isNoetherian

example : Prop :=
  IsNoetherian (TrivSqZeroExt (ℤ) (PUnit : Type 0))
    (RingHom.ker ((TrivSqZeroExt.fstHom ℕ (ℤ) (PUnit : Type 0)).toRingHom)) ↔
      IsNoetherian (ℤ) (PUnit : Type 0)

end ZeroModule

section IntegerRegular

example : Ring (ℤ) := inferInstance
example : AddCommMonoid (ℤ) := inferInstance
example : Module (ℤ) (ℤ) := inferInstance
example : Module (ℤ)ᵐᵒᵖ (ℤ) := inferInstance
example : SMulCommClass (ℤ) (ℤ)ᵐᵒᵖ (ℤ) := inferInstance

example :
  IsNoetherianRing (TrivSqZeroExt (ℤ) (ℤ)) ↔
    IsNoetherianRing (ℤ) ∧ Module.Finite (ℤ) (ℤ) :=
  TrivSqZeroExt.isNoetherianRing_iff

example :
  IsNoetherianRing (TrivSqZeroExt (ℤ) (ℤ)) ↔
    IsNoetherianRing (ℤ) ∧ IsNoetherian (ℤ) (ℤ) :=
  TrivSqZeroExt.isNoetherianRing_iff_isNoetherian

example : Prop :=
  IsNoetherian (TrivSqZeroExt (ℤ) (ℤ))
    (RingHom.ker ((TrivSqZeroExt.fstHom ℕ (ℤ) (ℤ)).toRingHom)) ↔
      IsNoetherian (ℤ) (ℤ)

end IntegerRegular

section IntegerTorsion

open scoped TrivSqZeroExt

example : Ring (ℤ) := inferInstance
example : AddCommMonoid (ZMod 2) := inferInstance
example : Module (ℤ) (ZMod 2) := inferInstance
example : Module (ℤ)ᵐᵒᵖ (ZMod 2) := inferInstance
example : SMulCommClass (ℤ) (ℤ)ᵐᵒᵖ (ZMod 2) := inferInstance

example :
  IsNoetherianRing (TrivSqZeroExt (ℤ) (ZMod 2)) ↔
    IsNoetherianRing (ℤ) ∧ Module.Finite (ℤ) (ZMod 2) :=
  TrivSqZeroExt.isNoetherianRing_iff

example :
  IsNoetherianRing (TrivSqZeroExt (ℤ) (ZMod 2)) ↔
    IsNoetherianRing (ℤ) ∧ IsNoetherian (ℤ) (ZMod 2) :=
  TrivSqZeroExt.isNoetherianRing_iff_isNoetherian

example : Prop :=
  IsNoetherian (TrivSqZeroExt (ℤ) (ZMod 2))
    (RingHom.ker ((TrivSqZeroExt.fstHom ℕ (ℤ) (ZMod 2)).toRingHom)) ↔
      IsNoetherian (ℤ) (ZMod 2)

end IntegerTorsion

section IntegerFinsupp

open scoped TrivSqZeroExt

example : Ring (ℤ) := inferInstance
example : AddCommMonoid (ℕ →₀ ℤ) := inferInstance
example : Module (ℤ) (ℕ →₀ ℤ) := inferInstance
example : Module (ℤ)ᵐᵒᵖ (ℕ →₀ ℤ) := inferInstance
example : SMulCommClass (ℤ) (ℤ)ᵐᵒᵖ (ℕ →₀ ℤ) := inferInstance

example :
  IsNoetherianRing (TrivSqZeroExt (ℤ) (ℕ →₀ ℤ)) ↔
    IsNoetherianRing (ℤ) ∧ Module.Finite (ℤ) (ℕ →₀ ℤ) :=
  TrivSqZeroExt.isNoetherianRing_iff

example :
  IsNoetherianRing (TrivSqZeroExt (ℤ) (ℕ →₀ ℤ)) ↔
    IsNoetherianRing (ℤ) ∧ IsNoetherian (ℤ) (ℕ →₀ ℤ) :=
  TrivSqZeroExt.isNoetherianRing_iff_isNoetherian

example : Prop :=
  IsNoetherian (TrivSqZeroExt (ℤ) (ℕ →₀ ℤ))
    (RingHom.ker ((TrivSqZeroExt.fstHom ℕ (ℤ) (ℕ →₀ ℤ)).toRingHom)) ↔
      IsNoetherian (ℤ) (ℕ →₀ ℤ)

end IntegerFinsupp

section MatrixRegular

example : Fintype (Fin 2) := inferInstance
example : DecidableEq (Fin 2) := inferInstance

example : Ring (Matrix (Fin 2) (Fin 2) ℤ) := inferInstance
example : AddCommMonoid (Matrix (Fin 2) (Fin 2) ℤ) := inferInstance
example : Module (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ) := inferInstance
example : Module (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ (Matrix (Fin 2) (Fin 2) ℤ) := inferInstance
example : SMulCommClass (Matrix (Fin 2) (Fin 2) ℤ)
    (Matrix (Fin 2) (Fin 2) ℤ)ᵐᵒᵖ (Matrix (Fin 2) (Fin 2) ℤ) := inferInstance

example :
  IsNoetherianRing (TrivSqZeroExt (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ)) ↔
    IsNoetherianRing (Matrix (Fin 2) (Fin 2) ℤ) ∧
      Module.Finite (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ) :=
  TrivSqZeroExt.isNoetherianRing_iff

example :
  IsNoetherianRing (TrivSqZeroExt (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ)) ↔
    IsNoetherianRing (Matrix (Fin 2) (Fin 2) ℤ) ∧
      IsNoetherian (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ) :=
  TrivSqZeroExt.isNoetherianRing_iff_isNoetherian

example : Prop :=
  IsNoetherian (TrivSqZeroExt (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ))
    (RingHom.ker ((TrivSqZeroExt.fstHom ℕ
      (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ)).toRingHom)) ↔
      IsNoetherian (Matrix (Fin 2) (Fin 2) ℤ) (Matrix (Fin 2) (Fin 2) ℤ)

end MatrixRegular

section RaisedModule

open scoped TrivSqZeroExt

example : Ring (ℤ : Type 0) := inferInstance
example : AddCommMonoid (ULift.{1} ℤ : Type 1) := inferInstance
example : Module (ℤ : Type 0) (ULift.{1} ℤ : Type 1) := inferInstance
example : Module (ℤ : Type 0)ᵐᵒᵖ (ULift.{1} ℤ : Type 1) := inferInstance
example : SMulCommClass (ℤ : Type 0) (ℤ : Type 0)ᵐᵒᵖ (ULift.{1} ℤ : Type 1) := inferInstance

example :
  IsNoetherianRing (TrivSqZeroExt (ℤ : Type 0) (ULift.{1} ℤ : Type 1)) ↔
    IsNoetherianRing (ℤ : Type 0) ∧ Module.Finite (ℤ : Type 0) (ULift.{1} ℤ : Type 1) :=
  TrivSqZeroExt.isNoetherianRing_iff

example :
  IsNoetherianRing (TrivSqZeroExt (ℤ : Type 0) (ULift.{1} ℤ : Type 1)) ↔
    IsNoetherianRing (ℤ : Type 0) ∧ IsNoetherian (ℤ : Type 0) (ULift.{1} ℤ : Type 1) :=
  TrivSqZeroExt.isNoetherianRing_iff_isNoetherian

example : Prop :=
  IsNoetherian (TrivSqZeroExt (ℤ : Type 0) (ULift.{1} ℤ : Type 1))
    (RingHom.ker ((TrivSqZeroExt.fstHom ℕ (ℤ : Type 0) (ULift.{1} ℤ : Type 1)).toRingHom)) ↔
      IsNoetherian (ℤ : Type 0) (ULift.{1} ℤ : Type 1)

end RaisedModule

section RaisedRing

open scoped TrivSqZeroExt

/-- Scalar multiplication by lifted integers on the integers. -/
local instance liftedIntSMul : SMul (ULift.{1} ℤ : Type 1) ℤ :=
  SMul.comp ℤ (ULift.ringEquiv : ULift.{1} ℤ ≃+* ℤ).toRingHom

/-- The integer module over the lifted integer ring. -/
local instance liftedIntModule : Module (ULift.{1} ℤ : Type 1) ℤ :=
  Module.compHom ℤ (ULift.ringEquiv : ULift.{1} ℤ ≃+* ℤ).toRingHom

/-- Scalar multiplication by the opposite lifted integer ring on the integers. -/
local instance oppositeLiftedIntSMul : SMul (ULift.{1} ℤ : Type 1)ᵐᵒᵖ ℤ :=
  SMul.comp ℤ (RingEquiv.toOpposite (ULift.{1} ℤ)).symm.toRingHom

/-- The integer module over the opposite lifted integer ring. -/
local instance oppositeLiftedIntModule : Module (ULift.{1} ℤ : Type 1)ᵐᵒᵖ ℤ :=
  TrivSqZeroExt.canonicalOppositeModule

local instance : IsCentralScalar (ULift.{1} ℤ : Type 1) ℤ :=
  TrivSqZeroExt.canonicalCentralScalar

local instance : SMulCommClass (ULift.{1} ℤ : Type 1) ℤ ℤ :=
  SMul.comp.smulCommClass (M := ℤ) (α := ℤ) (β := ℤ)
    (ULift.ringEquiv : ULift.{1} ℤ ≃+* ℤ).toRingHom

local instance : SMulCommClass (ULift.{1} ℤ : Type 1) (ULift.{1} ℤ : Type 1) ℤ :=
  SMul.comp.smulCommClass' (M := ℤ) (α := ℤ) (β := ULift.{1} ℤ)
    (ULift.ringEquiv : ULift.{1} ℤ ≃+* ℤ).toRingHom

local instance : SMulCommClass (ULift.{1} ℤ : Type 1) (ULift.{1} ℤ : Type 1)ᵐᵒᵖ ℤ :=
  SMulCommClass.op_right

example : Ring (ULift.{1} ℤ : Type 1) := inferInstance
example : AddCommMonoid (ℤ : Type 0) := inferInstance
example : Module (ULift.{1} ℤ : Type 1) (ℤ : Type 0) := inferInstance
example : Module (ULift.{1} ℤ : Type 1)ᵐᵒᵖ (ℤ : Type 0) := inferInstance
example : SMulCommClass (ULift.{1} ℤ : Type 1)
    (ULift.{1} ℤ : Type 1)ᵐᵒᵖ (ℤ : Type 0) := inferInstance

example :
  IsNoetherianRing (TrivSqZeroExt (ULift.{1} ℤ : Type 1) (ℤ : Type 0)) ↔
    IsNoetherianRing (ULift.{1} ℤ : Type 1) ∧ Module.Finite (ULift.{1} ℤ : Type 1) (ℤ : Type 0) :=
  TrivSqZeroExt.isNoetherianRing_iff

example :
  IsNoetherianRing (TrivSqZeroExt (ULift.{1} ℤ : Type 1) (ℤ : Type 0)) ↔
    IsNoetherianRing (ULift.{1} ℤ : Type 1) ∧ IsNoetherian (ULift.{1} ℤ : Type 1) (ℤ : Type 0) :=
  TrivSqZeroExt.isNoetherianRing_iff_isNoetherian

example : Prop :=
  IsNoetherian (TrivSqZeroExt (ULift.{1} ℤ : Type 1) (ℤ : Type 0))
    (RingHom.ker ((TrivSqZeroExt.fstHom ℕ (ULift.{1} ℤ : Type 1) (ℤ : Type 0)).toRingHom)) ↔
      IsNoetherian (ULift.{1} ℤ : Type 1) (ℤ : Type 0)

end RaisedRing

section PolynomialZeroModule

open scoped TrivSqZeroExt

example : Ring (MvPolynomial ℕ ℤ) := inferInstance
example : AddCommMonoid (PUnit : Type 0) := inferInstance
example : Module (MvPolynomial ℕ ℤ) (PUnit : Type 0) := inferInstance
example : Module (MvPolynomial ℕ ℤ)ᵐᵒᵖ (PUnit : Type 0) := inferInstance
example : SMulCommClass (MvPolynomial ℕ ℤ) (MvPolynomial ℕ ℤ)ᵐᵒᵖ (PUnit : Type 0) := inferInstance

example :
  IsNoetherianRing (TrivSqZeroExt (MvPolynomial ℕ ℤ) (PUnit : Type 0)) ↔
    IsNoetherianRing (MvPolynomial ℕ ℤ) ∧ Module.Finite (MvPolynomial ℕ ℤ) (PUnit : Type 0) :=
  TrivSqZeroExt.isNoetherianRing_iff

example :
  IsNoetherianRing (TrivSqZeroExt (MvPolynomial ℕ ℤ) (PUnit : Type 0)) ↔
    IsNoetherianRing (MvPolynomial ℕ ℤ) ∧ IsNoetherian (MvPolynomial ℕ ℤ) (PUnit : Type 0) :=
  TrivSqZeroExt.isNoetherianRing_iff_isNoetherian

example : Prop :=
  IsNoetherian (TrivSqZeroExt (MvPolynomial ℕ ℤ) (PUnit : Type 0))
    (RingHom.ker ((TrivSqZeroExt.fstHom ℕ (MvPolynomial ℕ ℤ) (PUnit : Type 0)).toRingHom)) ↔
      IsNoetherian (MvPolynomial ℕ ℤ) (PUnit : Type 0)

end PolynomialZeroModule

section NaturalRegular

example : Semiring (ℕ) := inferInstance
example : AddCommMonoid (ℕ) := inferInstance
example : Module (ℕ) (ℕ) := inferInstance
example : Module (ℕ)ᵐᵒᵖ (ℕ) := inferInstance
example : SMulCommClass (ℕ) (ℕ)ᵐᵒᵖ (ℕ) := inferInstance

example : Prop :=
  IsNoetherian (TrivSqZeroExt (ℕ) (ℕ))
    (RingHom.ker ((TrivSqZeroExt.fstHom ℕ (ℕ) (ℕ)).toRingHom)) ↔
      IsNoetherian (ℕ) (ℕ)

end NaturalRegular

end CoherentModulesTest.TrivSqZeroExtNoetherian
