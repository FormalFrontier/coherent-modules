/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Associativity of trivial square-zero extensions

For a coefficient type with multiplication and an additive monoid with distributive left and
right scalar actions, multiplication on the trivial square-zero extension is associative exactly
when coefficient multiplication is associative, both actions respect multiplication, and the two
actions commute. The right action respects multiplication in the reversed order.

No commutativity of addition, coefficient zero or one, or identity law for either action is needed.
-/

@[expose] public section

universe u v

namespace TrivSqZeroExt

open MulOpposite

variable {R : Type u} {M : Type v}
  [coefficientMul : Mul R] [additiveMonoid : AddMonoid M]
  [leftAction : DistribSMul R M] [rightAction : DistribSMul Rᵐᵒᵖ M]

/-- Multiplication on a trivial square-zero extension is associative if and only if coefficient
multiplication is associative, the left and right actions respect multiplication, and those actions
commute. The right-action composition law reverses the order of the coefficients. -/
theorem mul_assoc_iff :
    (∀ x y z : TrivSqZeroExt R M, (x * y) * z = x * (y * z)) ↔
      (∀ a b c : R, (a * b) * c = a * (b * c)) ∧
      (∀ (a b : R) (m : M), (a * b) • m = a • (b • m)) ∧
      (∀ (a b : R) (m : M), op (a * b) • m = op b • (op a • m)) ∧
      SMulCommClass R Rᵐᵒᵖ M := by
  constructor
  · intro h
    -- Normalize the projections before specializing to coefficient-module pairs.
    have hfst (x y z : TrivSqZeroExt R M) := congrArg fst (h x y z)
    have hsnd (x y z : TrivSqZeroExt R M) := congrArg snd (h x y z)
    simp only [fst_mul] at hfst
    simp only [snd_mul, fst_mul] at hsnd
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a b c
      simpa only [fst_mk] using hfst (a, 0) (b, 0) (c, 0)
    · intro a b m
      simpa only [fst_mk, snd_mk, smul_zero, add_zero] using
        hsnd (a, 0) (b, 0) (b, m)
    · intro a b m
      simpa only [fst_mk, snd_mk, smul_zero, zero_add] using
        (hsnd (a, m) (a, 0) (b, 0)).symm
    · refine ⟨?_⟩
      intro a b m
      simpa only [fst_mk, snd_mk, smul_zero, add_zero, zero_add, op_unop] using
        (hsnd (a, 0) (a, m) (unop b, 0)).symm
  · rintro ⟨hR, hleft, hright, hcomm⟩ x y z
    let _ : SMulCommClass R Rᵐᵒᵖ M := hcomm
    apply ext
    · simpa only [fst_mul] using hR x.fst y.fst z.fst
    · simp only [snd_mul, fst_mul, smul_add, hleft, hright]
      rw [← smul_comm x.fst (op z.fst) y.snd, add_assoc]

end TrivSqZeroExt
