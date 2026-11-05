/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Commutativity of trivial square-zero extensions

For a type `R` with multiplication and a type `M` with commutative addition and an
additive identity, the multiplication on `TrivSqZeroExt R M` is commutative exactly
when multiplication on `R` is commutative and the two given scalar actions agree.
Both actions need only preserve the zero of `M`; neither additive associativity
nor compatibility between the actions is required. The coefficient and module
universes are independent.

The criterion keeps the given multiplication, addition, zero and scalar actions.
In particular, it does not choose a right action from the left one. No zero or
one on `R` is needed, and no unit or square-zero ideal is asserted at this level.
Mathlib's `TrivSqZeroExt.commMonoid`, `TrivSqZeroExt.commSemiring` and
`TrivSqZeroExt.commRing` provide the commutative structures under their stronger
hypotheses.

## References

This uses Mathlib's trivial square-zero extension formalization by Kenny Lau,
Eric Wieser, Antoine Chambert-Loir and María-Inés de Frutos-Fernández. The proof
uses its coordinate API and follows the coordinatewise approach of its
commutative-monoid construction.
-/

@[expose] public section

universe u v

namespace TrivSqZeroExt

variable {R : Type u} {M : Type v} [Mul R] [AddZeroClass M] [IsAddCommutative M]
  [leftAction : SMulZeroClass R M] [rightAction : SMulZeroClass Rᵐᵒᵖ M]

/-- Multiplication on a trivial square-zero extension is commutative if and only if
coefficient multiplication is commutative and the given left and right scalar actions
agree. Additive associativity, coefficient zero and one, and compatibility between
the actions are not required. -/
theorem isMulCommutative_iff :
    IsMulCommutative (TrivSqZeroExt R M) ↔
      IsMulCommutative R ∧ IsCentralScalar R M := by
  constructor
  · intro h
    have hcomm := _root_.isMulCommutative_iff.mp h
    constructor
    · apply _root_.isMulCommutative_iff.mpr
      intro r s
      simpa only [fst_mul, fst_inl] using
        congrArg fst (hcomm (inl r) (inl s))
    · constructor
      intro r m
      -- Equal coefficient coordinates avoid any assumption about a zero in `R`.
      have hm := congrArg snd (hcomm (inl r) (r, m))
      change r • m + MulOpposite.op r • (0 : M) =
        r • (0 : M) + MulOpposite.op r • m at hm
      simpa only [smul_zero, add_zero, zero_add] using hm.symm
  · rintro ⟨hR, hM⟩
    let _ : IsMulCommutative R := hR
    let _ : IsCentralScalar R M := hM
    apply _root_.isMulCommutative_iff.mpr
    intro x y
    apply ext
    · simpa only [fst_mul] using mul_comm' x.fst y.fst
    · simp only [snd_mul, op_smul_eq_smul]
      exact add_comm' _ _

end TrivSqZeroExt
