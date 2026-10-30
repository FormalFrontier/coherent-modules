/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.TensorProduct.FiniteSurjectivity
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Generation by pure tensors

A family generates a module if and only if its pure tensors with `P` generate the
corresponding tensor product, provided the quotient by the family's span is
finitely generated and every maximal ideal acts on `P` with proper image. The
index type may be infinite, and neither module need be finitely generated;
no flatness of `P` is required.

The proof applies finite-cokernel tensor-surjectivity reflection to Mathlib's
`Finsupp.linearCombination`, whose range is the span of the given family. The
pure-tensor span is computed using Mathlib's tensor-map range and bilinear-span
identities.
-/

@[expose] public section

universe uR uP uN uI

open scoped TensorProduct

namespace Submodule

/-- Generation by a family is reflected by its pure tensors with `P` when the
quotient by its span is finitely generated and every maximal ideal acts properly
on `P`. The family may be infinite, and neither module need be finitely generated. -/
theorem span_tmul_eq_top_iff_span_eq_top_of_finite_quotient
    {R : Type uR} [CommRing R]
    {P : Type uP} [AddCommMonoid P] [Module R P]
    {N : Type uN} [AddCommGroup N] [Module R N]
    {ι : Type uI} (v : ι → N)
    [Module.Finite R (N ⧸ Submodule.span R (Set.range v))]
    (hP : ∀ m : Ideal R, m.IsMaximal →
      m • (⊤ : Submodule R P) ≠ ⊤) :
    Submodule.span R
      (Set.range (fun x : P × ι => x.1 ⊗ₜ[R] v x.2)) = ⊤ ↔
      Submodule.span R (Set.range v) = ⊤ := by
  have hspan :
      LinearMap.range ((Finsupp.linearCombination R v).lTensor P) =
        Submodule.span R
          (Set.range (fun x : P × ι => x.1 ⊗ₜ[R] v x.2)) := by
    rw [LinearMap.lTensor_def, TensorProduct.range_map, LinearMap.range_id,
      Finsupp.range_linearCombination, ← Submodule.span_univ (R := R) (M := P),
      Submodule.map₂_span_span]
    congr 1
    ext t
    constructor
    · rintro ⟨p, _, n, ⟨i, rfl⟩, rfl⟩
      exact ⟨(p, i), rfl⟩
    · rintro ⟨⟨p, i⟩, rfl⟩
      exact ⟨p, Set.mem_univ p, v i, ⟨i, rfl⟩, rfl⟩
  let : Module.Finite R (N ⧸ LinearMap.range (Finsupp.linearCombination R v)) := by
    rw [Finsupp.range_linearCombination]
    infer_instance
  rw [← hspan, LinearMap.range_eq_top,
    span_range_eq_top_iff_surjective_finsuppLinearCombination]
  exact LinearMap.lTensor_surjective_iff_surjective_of_finite_cokernel
    (Finsupp.linearCombination R v) hP

end Submodule
