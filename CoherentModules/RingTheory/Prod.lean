/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.RingTheory.Pi
public import CoherentModules.LinearAlgebra.Prod
public import CoherentModules.LinearAlgebra.ULift
import Mathlib.Algebra.Ring.Equiv

/-!
# Coherence over a binary product of rings

The canonical module `Module.prodRing` on `M × N` over `A × B` is coherent exactly
when the original `A`-module `M` and `B`-module `N` are coherent. The regular-module
specialization gives the corresponding criterion for coherent rings.

The proof compares the binary product with a dependent product indexed by
`Option Unit`, using separate universe lifts for the coefficient rings and module
carriers, and applies `Module.IsCoherent.piRing_iff`. The four original universes
are independent, and the rings need not be commutative. The comparison retains the
given additive commutative monoids and module actions.

## References

* Fujiwara–Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
  Proposition 0.3.3.2(1), printed p. 103. The binary criterion here extends the
  commutative, fixed-universe statement to possibly noncommutative rings and four
  independent coefficient and carrier universes.
* `Module.IsCoherent.piRing_iff`, together with Mathlib's Option, singleton,
  product and `ULift` equivalences.
-/

@[expose] public section

universe uA uB uM uN vA vM

namespace Module.IsCoherent

section Lift

variable (A : Type uA) (M : Type uM) [Ring A] [AddCommMonoid M] [Module A M]

local instance : RingHomInvPair
    (ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom
    (ULift.ringEquiv : ULift.{vA} A ≃+* A).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (ULift.ringEquiv : ULift.{vA} A ≃+* A)

local instance : RingHomInvPair
    (ULift.ringEquiv : ULift.{vA} A ≃+* A).symm.toRingHom
    (ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (ULift.ringEquiv : ULift.{vA} A ≃+* A)

private theorem ulift_iff :
    Module.IsCoherent (ULift.{vA} A) (ULift.{vM} M) ↔ Module.IsCoherent A M :=
  semilinearEquiv_iff
    (σ' := (ULift.ringEquiv : ULift.{vA} A ≃+* A).symm.toRingHom)
    (ULift.semilinearModuleEquiv A M :
      ULift.{vM} M ≃ₛₗ[(ULift.ringEquiv : ULift.{vA} A ≃+* A).toRingHom] M)

end Lift

private abbrev Scalar (A : Type uA) (B : Type uB) : Option Unit → Type (max uA uB)
  | none => ULift.{max uA uB} A
  | some _ => ULift.{max uA uB} B

private abbrev Carrier (M : Type uM) (N : Type uN) : Option Unit → Type (max uM uN)
  | none => ULift.{max uM uN} M
  | some _ => ULift.{max uM uN} N

section Structures

variable (A : Type uA) (B : Type uB) (M : Type uM) (N : Type uN)

private abbrev scalarRing [Ring A] [Ring B] (i : Option Unit) : Ring (Scalar A B i) :=
  match i with
  | none => inferInstance
  | some _ => inferInstance

private abbrev carrierAddCommMonoid [AddCommMonoid M] [AddCommMonoid N] (i : Option Unit) :
    AddCommMonoid (Carrier M N i) :=
  match i with
  | none => inferInstance
  | some _ => inferInstance

attribute [local instance] scalarRing carrierAddCommMonoid

private abbrev carrierModule [Ring A] [Ring B] [AddCommMonoid M] [AddCommMonoid N]
    [Module A M] [Module B N] (i : Option Unit) : Module (Scalar A B i) (Carrier M N i) :=
  match i with
  | none => @ULift.module A (ULift.{max uM uN} M) inferInstance inferInstance
      (@ULift.module' A M inferInstance inferInstance inferInstance)
  | some _ => @ULift.module B (ULift.{max uM uN} N) inferInstance inferInstance
      (@ULift.module' B N inferInstance inferInstance inferInstance)

end Structures

attribute [local instance] scalarRing carrierAddCommMonoid carrierModule

private def scalarEquiv (A : Type uA) (B : Type uB) [Ring A] [Ring B] :
    (∀ i, Scalar A B i) ≃+* (A × B) :=
  (RingEquiv.piOptionEquivProd (R := Scalar A B)).trans
    (RingEquiv.prodCongr
      (ULift.ringEquiv : ULift.{max uA uB} A ≃+* A)
      ((RingEquiv.piUnique (fun _ : Unit => ULift.{max uA uB} B)).trans
        (ULift.ringEquiv : ULift.{max uA uB} B ≃+* B)))

private def carrierEquiv (M : Type uM) (N : Type uN)
    [AddCommMonoid M] [AddCommMonoid N] : (∀ i, Carrier M N i) ≃+ (M × N) where
  __ := (Equiv.piOptionEquivProd (β := Carrier M N)).trans
    (Equiv.prodCongr Equiv.ulift
      ((Equiv.piUnique (fun _ : Unit => ULift.{max uM uN} N)).trans Equiv.ulift))
  map_add' _ _ := rfl

section Modules

variable (A : Type uA) (B : Type uB) (M : Type uM) (N : Type uN)
variable [Ring A] [Ring B] [AddCommMonoid M] [AddCommMonoid N]
variable [Module A M] [Module B N]

attribute [local instance] Module.prodRing

private theorem scalarEquiv_invPair : RingHomInvPair (scalarEquiv A B).toRingHom
    (scalarEquiv A B).symm.toRingHom := RingHomInvPair.of_ringEquiv (scalarEquiv A B)

private theorem scalarEquiv_invPair_symm : RingHomInvPair (scalarEquiv A B).symm.toRingHom
    (scalarEquiv A B).toRingHom := RingHomInvPair.of_ringEquiv_symm (scalarEquiv A B)

attribute [local instance] scalarEquiv_invPair scalarEquiv_invPair_symm

private def moduleEquiv :
    (∀ i, Carrier M N i) ≃ₛₗ[(scalarEquiv A B).toRingHom] (M × N) where
  __ := carrierEquiv M N
  map_smul' _ _ := rfl

/-- The canonical binary module over a product of rings is coherent exactly when
both factors are coherent over their original rings.

This extends Fujiwara–Kato, *Foundations of Rigid Geometry I*, arXiv:1308.4734v5,
Proposition 0.3.3.2(1), printed p. 103, from commutative rings in a fixed universe
to possibly noncommutative rings and four independent coefficient and carrier
universes. No separate finite-generation assumptions are needed: coherence gives
finite generation by `Module.IsCoherent.toFinite`, and `Module.Finite.prodRing_iff`
compares finite generation of this canonical product with that of its factors. -/
theorem prodRing_iff :
    Module.IsCoherent (A × B) (M × N) ↔ Module.IsCoherent A M ∧ Module.IsCoherent B N := by
  have hA : Module.IsCoherent (Scalar A B none) (Carrier M N none) ↔
      Module.IsCoherent A M := ulift_iff A M
  have hB : Module.IsCoherent (Scalar A B (some ())) (Carrier M N (some ())) ↔
      Module.IsCoherent B N := ulift_iff B N
  calc
    Module.IsCoherent (A × B) (M × N) ↔
        Module.IsCoherent (∀ i, Scalar A B i) (∀ i, Carrier M N i) :=
      (semilinearEquiv_iff
        (σ' := (scalarEquiv A B).symm.toRingHom) (moduleEquiv A B M N)).symm
    _ ↔ ∀ i, Module.IsCoherent (Scalar A B i) (Carrier M N i) := piRing_iff
    _ ↔ Module.IsCoherent A M ∧ Module.IsCoherent B N := by
      constructor
      · intro h
        exact ⟨hA.mp (h none), hB.mp (h (some ()))⟩
      · rintro ⟨hM, hN⟩ i
        cases i with
        | none => exact hA.mpr hM
        | some i =>
          cases i
          exact hB.mpr hN

end Modules

private theorem isCoherentRing_prod_iff (A : Type uA) (B : Type uB) [Ring A] [Ring B] :
    IsCoherentRing (A × B) ↔ IsCoherentRing A ∧ IsCoherentRing B := by
  constructor
  · intro h
    let : IsCoherentRing (A × B) := h
    have hpi : IsCoherentRing (∀ i, Scalar A B i) :=
      IsCoherentRing.of_ringEquiv (scalarEquiv A B).symm
    have hc := isCoherentRing_pi_iff.mp hpi
    let : IsCoherentRing (Scalar A B none) := hc none
    let : IsCoherentRing (Scalar A B (some ())) := hc (some ())
    exact ⟨IsCoherentRing.of_ringEquiv
      (ULift.ringEquiv : ULift.{max uA uB} A ≃+* A),
      IsCoherentRing.of_ringEquiv
        (ULift.ringEquiv : ULift.{max uA uB} B ≃+* B)⟩
  · rintro ⟨hA, hB⟩
    let : IsCoherentRing A := hA
    let : IsCoherentRing B := hB
    have hc (i : Option Unit) : IsCoherentRing (Scalar A B i) := by
      cases i with
      | none =>
        exact IsCoherentRing.of_ringEquiv
          (ULift.ringEquiv : ULift.{max uA uB} A ≃+* A).symm
      | some i =>
        cases i
        exact IsCoherentRing.of_ringEquiv
          (ULift.ringEquiv : ULift.{max uA uB} B ≃+* B).symm
    let : IsCoherentRing (∀ i, Scalar A B i) := isCoherentRing_pi_iff.mpr hc
    exact IsCoherentRing.of_ringEquiv (scalarEquiv A B)

end Module.IsCoherent

/-- A binary product of possibly noncommutative rings is coherent exactly when
both factors are coherent. This is the regular-module specialization of
`Module.IsCoherent.prodRing_iff`, using the usual multiplication action. -/
theorem isCoherentRing_prod_iff (A : Type uA) (B : Type uB) [Ring A] [Ring B] :
    IsCoherentRing (A × B) ↔ IsCoherentRing A ∧ IsCoherentRing B :=
  Module.IsCoherent.isCoherentRing_prod_iff A B
