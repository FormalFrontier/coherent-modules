/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Basic
public import CoherentModules.LinearAlgebra.DirectSum

/-!
# Coherence of dependent direct sums

A direct sum over a ring is coherent if and only if every summand is coherent and only
finitely many summands are nontrivial. The index type is arbitrary, and the ring need not
be commutative. The given additive commutative monoids and module actions are retained.

## Main declarations

* `Module.IsCoherent.of_directSum`: coherence descends to each summand.
* `Module.IsCoherent.directSum_iff`: the coherence criterion for an arbitrary dependent sum.

## Implementation notes

The coordinate argument uses the canonical singleton inclusion and coefficient projection.
The converse removes subsingleton summands with
`DirectSum.linearEquivOfSubsingletonComplement`, then uses Mathlib's finite-sum/product
comparison and the finite-product closure theorem. Additive group structures needed by
these closure APIs are derived locally from the original ring actions.
-/

@[expose] public section

universe uι uR uM

namespace Module.IsCoherent

variable {ι : Type uι} {R : Type uR} {M : ι → Type uM}
    [Ring R] [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- Each summand of a coherent direct sum is coherent over the same ring, with its given
module structure. No finiteness assumption on the index type is needed. -/
theorem of_directSum [Module.IsCoherent R (DirectSum ι M)] (i : ι) :
    Module.IsCoherent R (M i) := by
  classical
  let : AddCommGroup (M i) := Module.addCommMonoidToAddCommGroup R (M := M i)
  let : AddCommGroup (DirectSum ι M) :=
    Module.addCommMonoidToAddCommGroup R (M := DirectSum ι M)
  have hleft : Function.LeftInverse (DirectSum.component R ι M i)
      (DirectSum.lof R ι M i) := by
    intro m
    exact DirectSum.component.lof_self (R := R) (ι := ι) (M := M) i m
  let _ : Module.Finite R (M i) :=
    Module.Finite.of_surjective (DirectSum.component R ι M i)
      (fun m ↦ ⟨DirectSum.lof R ι M i m, hleft m⟩)
  let _ : Module.IsCoherent R (LinearMap.range (DirectSum.lof R ι M i)) :=
    Module.IsCoherent.range (DirectSum.lof R ι M i)
  exact Module.IsCoherent.of_equiv
    (LinearEquiv.ofLeftInverse (f := DirectSum.lof R ι M i) hleft).symm

/-- A dependent direct sum is coherent exactly when all its summands are coherent and the
set of nontrivial summands is finite. Coherence includes finite generation and finite
presentation of every finitely generated submodule, not just of the whole module. -/
theorem directSum_iff :
    Module.IsCoherent R (DirectSum ι M) ↔
      (∀ i, Module.IsCoherent R (M i)) ∧ Set.Finite {i | ¬ Subsingleton (M i)} := by
  classical
  constructor
  · intro h
    let _ : Module.IsCoherent R (DirectSum ι M) := h
    exact ⟨fun i ↦ of_directSum (R := R) (M := M) i,
      Module.Finite.finite_nontrivial_summands (R := R) (M := M)⟩
  · rintro ⟨hM, hActive⟩
    let : ∀ i, AddCommGroup (M i) :=
      fun i ↦ Module.addCommMonoidToAddCommGroup R (M := M i)
    let : AddCommGroup (DirectSum ι M) :=
      Module.addCommMonoidToAddCommGroup R (M := DirectSum ι M)
    let : Fintype {i : ι // ¬ Subsingleton (M i)} := hActive.fintype
    let : ∀ i : {i : ι // ¬ Subsingleton (M i)}, Module.IsCoherent R (M i.val) :=
      fun i ↦ hM i.val
    let _ : Module.IsCoherent R (∀ i : {i : ι // ¬ Subsingleton (M i)}, M i.val) :=
      Module.IsCoherent.pi
    have hOff : ∀ i, i ∉ Set.range
        (Subtype.val : {i : ι // ¬ Subsingleton (M i)} → ι) → Subsingleton (M i) := by
      intro i hi
      by_contra h
      exact hi ⟨⟨i, h⟩, rfl⟩
    let e : DirectSum ι M ≃ₗ[R] (∀ i : {i : ι // ¬ Subsingleton (M i)}, M i.val) :=
      (DirectSum.linearEquivOfSubsingletonComplement R M
        (⟨Subtype.val, Subtype.val_injective⟩ : {i : ι // ¬ Subsingleton (M i)} ↪ ι)
        hOff).symm.trans
        (DirectSum.linearEquivFunOnFintype R {i : ι // ¬ Subsingleton (M i)}
          (fun i ↦ M i.val))
    exact Module.IsCoherent.of_equiv e.symm

end Module.IsCoherent
