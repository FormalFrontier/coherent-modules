/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Module.Prod
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Ring.Prod
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Binary products over different coefficient semirings

`Module.prodRing` equips `M × N` with the coordinatewise action of `A × B`,
using the given `A`-module structure on `M` and `B`-module structure on `N`.
The coefficient semirings and module carriers have four independent universes.

The semilinear coordinate projections and the actions of `(1, 0)` and `(0, 1)`
characterize this action. `Module.Finite.prodRing_iff` says that this product is
finitely generated if and only if both original factors are finitely generated.

## Implementation notes

The module structure is a reducible non-instance, assembled from Mathlib's
`Module.compHom` and `Prod.instModule`. It is selected only locally; no
heterogeneous product-module instance is registered globally. The
finite-generation comparison uses Mathlib's semilinear finite-generation
transport and common-scalar product instance.
-/

@[expose] public section

universe uA uB uM uN

namespace Module

/-- The module on `M × N` over `A × B` obtained by pulling the given actions
back along the scalar projections and taking the product module.
This is a reducible non-instance, like `Module.compHom`. -/
abbrev prodRing (A : Type uA) (B : Type uB) (M : Type uM) (N : Type uN)
    [Semiring A] [Semiring B] [AddCommMonoid M] [AddCommMonoid N]
    [Module A M] [Module B N] : Module (A × B) (M × N) :=
  @Prod.instModule (A × B) M N inferInstance inferInstance inferInstance
    (Module.compHom M (RingHom.fst A B)) (Module.compHom N (RingHom.snd A B))

section Coordinates

variable (A : Type uA) (B : Type uB) (M : Type uM) (N : Type uN)
variable [Semiring A] [Semiring B] [AddCommMonoid M] [AddCommMonoid N]
variable [Module A M] [Module B N]

attribute [local instance] prodRing

/-- The product action uses the given action in each coordinate. -/
theorem prodRing_smul (r : A × B) (x : M × N) :
    r • x = (r.1 • x.1, r.2 • x.2) := rfl

/-- First-coordinate action agreement for the projection-pullback product. -/
theorem prodRing_smul_fst (r : A × B) (x : M × N) :
    (r • x).1 = r.1 • x.1 := rfl

/-- Second-coordinate action agreement for the projection-pullback product. -/
theorem prodRing_smul_snd (r : A × B) (x : M × N) :
    (r • x).2 = r.2 • x.2 := rfl

/-- Projection to the given `A`-module, semilinear over the first scalar projection. -/
def prodRingFst : (M × N) →ₛₗ[RingHom.fst A B] M where
  toFun := Prod.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Projection to the given `B`-module, semilinear over the second scalar projection. -/
def prodRingSnd : (M × N) →ₛₗ[RingHom.snd A B] N where
  toFun := Prod.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The first semilinear projection is the first-coordinate map. -/
@[simp]
theorem prodRingFst_apply (x : M × N) : prodRingFst A B M N x = x.1 := rfl

/-- The second semilinear projection is the second-coordinate map. -/
@[simp]
theorem prodRingSnd_apply (x : M × N) : prodRingSnd A B M N x = x.2 := rfl

/-- The first central idempotent isolates the first module coordinate. -/
theorem prodRing_smul_left (x : M × N) : ((1, 0) : A × B) • x = (x.1, 0) := by
  change ((1 : A) • x.1, (0 : B) • x.2) = _
  rw [one_smul, zero_smul]

/-- The second central idempotent isolates the second module coordinate. -/
theorem prodRing_smul_right (x : M × N) : ((0, 1) : A × B) • x = (0, x.2) := by
  change ((0 : A) • x.1, (1 : B) • x.2) = _
  rw [zero_smul, one_smul]

/-- The coordinatewise product over `A × B` is finitely generated if and only
if each factor is finitely generated over its own coefficient semiring. -/
theorem Finite.prodRing_iff :
    Module.Finite (A × B) (M × N) ↔ Module.Finite A M ∧ Module.Finite B N := by
  constructor
  · intro h
    let : Module.Finite (A × B) (M × N) := h
    exact ⟨Module.Finite.of_surjective (prodRingFst A B M N) (fun m => ⟨(m, 0), rfl⟩),
      Module.Finite.of_surjective (prodRingSnd A B M N) (fun n => ⟨(0, n), rfl⟩)⟩
  · rintro ⟨hM, hN⟩
    let : Module (A × B) M := Module.compHom M (RingHom.fst A B)
    let : Module (A × B) N := Module.compHom N (RingHom.snd A B)
    let fst : M →ₛₗ[RingHom.fst A B] M :=
      { toFun := fun m => m
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    let snd : N →ₛₗ[RingHom.snd A B] N :=
      { toFun := fun n => n
        map_add' _ _ := rfl
        map_smul' _ _ := rfl }
    -- The identity maps compare the projection pullbacks with the given actions.
    let : Module.Finite (A × B) M :=
      (LinearMap.finite_iff_of_bijective fst
        ⟨fun _ _ h => h, fun m => ⟨m, rfl⟩⟩).mpr hM
    let : Module.Finite (A × B) N :=
      (LinearMap.finite_iff_of_bijective snd
        ⟨fun _ _ h => h, fun n => ⟨n, rfl⟩⟩).mpr hN
    exact Module.Finite.prod

end Coordinates

/-- For the regular modules, `prodRing` agrees with the regular module of the
product semiring. -/
theorem prodRing_regular (A : Type uA) (B : Type uB) [Semiring A] [Semiring B] :
    prodRing A B A B = (inferInstance : Module (A × B) (A × B)) :=
  Module.ext' _ _ (fun _ _ => rfl)

end Module
