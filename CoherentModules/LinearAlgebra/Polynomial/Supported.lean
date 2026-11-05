/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Set.Finite.Range

/-!
# Monomial shifts supported in bounded degrees

In a free left module over a polynomial semiring, a monomial shift by more than
`D` cannot have all its coefficients supported in degrees at most `D` unless it
is zero. Consequently, the monomial shifts of a finite family whose coefficients
vanish outside a degree-bounded set of coordinates form a finite set.

The coefficient semiring need not be commutative. Neither the module's coordinate
type nor the set of allowed coefficient coordinates is assumed finite. Scalar
multiplication is the pointwise left multiplication action of polynomials.
-/

@[expose] public section

universe u v w

namespace Polynomial

variable {R : Type u} [Semiring R] {I : Type v} {ι : Type w}

/-- A monomial shift supported in a degree-bounded set of coefficient coordinates
is zero if the shift exponent exceeds the degree bound. -/
theorem X_pow_smul_eq_zero_of_coeff_eq_zero_outside (v : I →₀ R[X])
    {J : Set (I × ℕ)} {D n : ℕ} (hJ : ∀ p ∈ J, p.2 ≤ D) (hn : D < n)
    (hv : ∀ p ∉ J, ((((X : R[X]) ^ n) • v) p.1).coeff p.2 = 0) :
    ((X : R[X]) ^ n) • v = 0 := by
  apply Finsupp.ext
  intro i
  apply Polynomial.ext
  intro k
  by_cases hk : n ≤ k
  · have hp : (i, k) ∉ J := by
      intro hp
      exact (not_le_of_gt (hn.trans_le hk)) (hJ (i, k) hp)
    simpa only [Finsupp.zero_apply, coeff_zero] using hv (i, k) hp
  · simp only [Finsupp.smul_apply, smul_eq_mul, coeff_X_pow_mul', ite_eq_right hk,
      Finsupp.zero_apply, coeff_zero]

/-- The monomial shifts of a finite family that vanish outside a degree-bounded
set of coefficient coordinates form a finite set. This does not require the
coordinate type or the set of allowed coordinates to be finite. -/
theorem finite_range_X_pow_smul_inter [Finite ι] (g : ι → I →₀ R[X])
    {J : Set (I × ℕ)} {D : ℕ} (hJ : ∀ p ∈ J, p.2 ≤ D) :
    (Set.range (fun p : ι × ℕ => ((X : R[X]) ^ p.2) • g p.1) ∩
      {v | ∀ p ∉ J, (v p.1).coeff p.2 = 0}).Finite := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let f : ι × Fin (D + 1) → I →₀ R[X] :=
    fun p => ((X : R[X]) ^ (p.2 : ℕ)) • g p.1
  refine ((Set.finite_range f).insert 0).subset ?_
  rintro v ⟨⟨⟨i, n⟩, rfl⟩, hv⟩
  by_cases hn : n ≤ D
  · right
    exact ⟨(i, ⟨n, Nat.lt_succ_of_le hn⟩), rfl⟩
  · left
    exact X_pow_smul_eq_zero_of_coeff_eq_zero_outside (g i) hJ (lt_of_not_ge hn) hv

end Polynomial
