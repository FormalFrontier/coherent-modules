/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.DirectSum

/-!
# Nonzero integer coefficients across a zero complement

Use the top integer submodule in nonnegative degrees and the bottom submodule in negative
degrees. The natural-number inclusion omits degree `-1`, while the singleton with coefficient
`1` in degree zero remains nonzero under the direct-sum equivalence.
-/

@[expose] public section

namespace DirectSum

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The integer submodule is full in nonnegative degrees and zero in negative degrees. -/
noncomputable def intPiece (k : ℤ) : Submodule ℤ ℤ :=
  if 0 ≤ k then ⊤ else ⊥

private theorem intPiece_subsingleton_of_neg (k : ℤ) (hk : k < 0) :
    Subsingleton (intPiece k) := by
  simpa [intPiece, not_le.mpr hk] using
    (inferInstance : Subsingleton (↥(⊥ : Submodule ℤ ℤ)))

private noncomputable def zeroPieceOne : intPiece 0 :=
  ⟨1, by simp [intPiece]⟩

/-- An omitted negative degree coexists with a retained nonzero singleton. -/
private theorem nonzero_retained_singleton :
    (-1 : ℤ) ∉ Set.range (Nat.castEmbedding : ℕ ↪ ℤ) ∧
      linearEquivIntOfSubsingletonNeg ℤ (fun k ↦ ↥(intPiece k))
        intPiece_subsingleton_of_neg
        (lof ℤ ℕ (fun n ↦ ↥(intPiece (n : ℤ))) 0 zeroPieceOne) ≠ 0 := by
  constructor
  · rintro ⟨n, hn⟩
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := Int.natCast_nonneg n
    change (n : ℤ) = -1 at hn
    rw [hn] at hn0
    exact (by decide : ¬ ((0 : ℤ) ≤ -1)) hn0
  · rw [linearEquivIntOfSubsingletonNeg_lof]
    intro h
    have hv := congrArg (fun f : ⨁ k : ℤ, ↥(intPiece k) ↦ (f 0).val) h
    simp [zeroPieceOne] at hv

end DirectSum
