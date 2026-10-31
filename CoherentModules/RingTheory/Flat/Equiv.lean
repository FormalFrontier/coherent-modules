/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RingTheory.Flat.Stability

/-!
# Flatness under semilinear equivalences

`Module.Flat.of_semilinearEquiv` transports flatness from the target of a
semilinear equivalence to its source, allowing equivalent coefficient semirings.
`Module.Flat.semilinearEquiv_iff` packages both directions. The two given module
actions are retained. For the identity coefficient equivalence, the same ordinary
linear equivalence is accepted, as in `Module.Flat.of_linearEquiv` and
`Module.Flat.equiv_iff`.

## Implementation notes

Over commutative semirings, Mathlib's `Module.Flat` denotes mono-flatness
(preservation of injective linear maps by tensoring); over rings this is usual
flatness. The proof uses restriction of scalars on an auxiliary copy, the
coefficient equivalence on regular modules, and composition of flatness. No
auxiliary action or scalar tower is required on either given module.

## References

The proof reuses Mathlib's `Module.Flat.of_linearEquiv`, `Module.Flat.trans`,
`Module.compHom.toLinearEquiv`, `RestrictScalars` and `AddEquiv.toLinearEquiv`.
See the library credits for the authors of these formalizations.
-/

@[expose] public section

universe uR uS uM uN

/-- A module semilinearly equivalent to a flat module over equivalent
commutative semirings is flat for its given scalar action. -/
theorem Module.Flat.of_semilinearEquiv
    {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN}
    [commR : CommSemiring R] [commS : CommSemiring S]
    [addM : AddCommMonoid M] [addN : AddCommMonoid N]
    [moduleM : Module R M] [moduleN : Module S N]
    [flatN : @Module.Flat S N commS addN moduleN]
    (e : R ≃+* S)
    (E : @LinearEquiv R S commR.toSemiring commS.toSemiring
      e.toRingHom e.symm.toRingHom
      (RingHomInvPair.of_ringEquiv e)
      (RingHomInvPair.of_ringEquiv_symm e)
      M N addM addN moduleM moduleN) :
    @Module.Flat R M commR addM moduleM := by
  -- This algebra changes only the regular coefficient action on `S`.
  let : Algebra R S := e.toRingHom.toAlgebra
  let T : R ≃ₗ[R] S := Module.compHom.toLinearEquiv e
  have : Module.Flat R S := Module.Flat.of_linearEquiv T.symm
  -- Keep the given `S`-action on the copy, and restrict its other action along `e`.
  let B := RestrictScalars R S N
  let : Module S B := RestrictScalars.moduleOrig R S N
  let : Module R B := RestrictScalars.module R S N
  -- The restriction tower is `(e r * s) • n = e r • (s • n)`, by `mul_smul`.
  let : IsScalarTower R S B := RestrictScalars.isScalarTower R S N
  let j : B ≃ₗ[S] N :=
    (RestrictScalars.addEquiv R S N).toLinearEquiv (fun _ _ ↦ rfl)
  have : Module.Flat S B := Module.Flat.of_linearEquiv j
  have : Module.Flat R B := Module.Flat.trans R S B
  -- Supply the canonical witnesses locally for the semilinear projection API.
  let : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  let : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.of_ringEquiv_symm e
  -- Semilinearity makes `E` linear into the restricted copy, not a new action on `N`.
  let F : M ≃ₗ[R] B :=
    (E.toAddEquiv.trans (RestrictScalars.addEquiv R S N).symm).toLinearEquiv
      (fun r m ↦
        (congrArg (RestrictScalars.addEquiv R S N).symm (E.map_smul' r m)).trans
          (RestrictScalars.addEquiv_symm_map_algebraMap_smul R S N r (E.toAddEquiv m)))
  exact Module.Flat.of_linearEquiv F

/-- Flatness is invariant under equivalent commutative semirings and a
compatible semilinear equivalence, with both given scalar actions retained. -/
theorem Module.Flat.semilinearEquiv_iff
    {R : Type uR} {S : Type uS} {M : Type uM} {N : Type uN}
    [commR : CommSemiring R] [commS : CommSemiring S]
    [addM : AddCommMonoid M] [addN : AddCommMonoid N]
    [moduleM : Module R M] [moduleN : Module S N]
    (e : R ≃+* S)
    (E : @LinearEquiv R S commR.toSemiring commS.toSemiring
      e.toRingHom e.symm.toRingHom
      (RingHomInvPair.of_ringEquiv e)
      (RingHomInvPair.of_ringEquiv_symm e)
      M N addM addN moduleM moduleN) :
    @Module.Flat R M commR addM moduleM ↔
      @Module.Flat S N commS addN moduleN := by
  constructor
  · intro hM
    let : @Module.Flat R M commR addM moduleM := hM
    exact Module.Flat.of_semilinearEquiv e.symm E.symm
  · intro hN
    let : @Module.Flat S N commS addN moduleN := hN
    exact Module.Flat.of_semilinearEquiv e E
