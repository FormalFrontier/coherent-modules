/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Basic
public import CoherentModules.LinearAlgebra.Matrix.Entrywise

/-!
# Coherence of finite matrix rings

Finite square matrix rings over left coherent rings are left coherent, including
empty matrix indices. For a nonempty finite index type, the converse holds as well.
The coefficient ring may be noncommutative or zero, and its universe is independent
of the matrix-index universe.

## Main declarations

* `Matrix.instIsCoherentRing`: preservation of left ring coherence by finite matrices.
* `IsCoherentRing.of_matrix`: reflection for a nonempty finite matrix index.
* `Matrix.isCoherentRing_iff`: the resulting equivalence for nonempty indices.

## Implementation notes

Preservation uses finite-product coherence over the coefficient ring and coherence
ascent along the canonical scalar tower. Reflection applies the finite-free kernel
criterion to the entrywise lift and descends finite generation through its split
kernel entry projection. Only reflection chooses an index. No reverse typeclass
instance is installed, to avoid a loop with preservation.

## References

The proof uses this library's finite-free kernel criterion and scalar-ascent theorem,
together with Mathlib's finite-product, scalar-restriction and matrix-module APIs.
-/

@[expose] public section

universe uR uI

variable {R : Type uR} {ι : Type uI} [Ring R] [Fintype ι] [DecidableEq ι]

namespace Matrix

/-- Finite square matrices over a left coherent ring form a left coherent ring.
The matrix index is allowed to be empty. -/
instance instIsCoherentRing [IsCoherentRing R] : IsCoherentRing (Matrix ι ι R) := by
  let _ : Module.Finite R (Matrix ι ι R) :=
    inferInstanceAs (Module.Finite R (ι → ι → R))
  let _ : Module.IsCoherent R (Matrix ι ι R) :=
    inferInstanceAs (Module.IsCoherent R (ι → ι → R))
  exact ⟨Module.IsCoherent.of_restrictScalars R⟩

end Matrix

/-- If a nonempty finite square matrix ring is left coherent, then so is its
coefficient ring. Coherence concerns the original regular left modules. -/
theorem IsCoherentRing.of_matrix [Nonempty ι] [IsCoherentRing (Matrix ι ι R)] :
    IsCoherentRing R := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  let _ : Module.Finite R (Matrix ι ι R) :=
    inferInstanceAs (Module.Finite R (ι → ι → R))
  refine ⟨Module.IsCoherent.iff_finite_and_fg_ker.mpr ⟨inferInstance, ?_⟩⟩
  intro n f
  have hG : (LinearMap.ker (Matrix.entrywiseLinearMap (ι := ι) f)).FG :=
    (Module.IsCoherent.iff_finite_and_fg_ker.mp
      (inferInstance : Module.IsCoherent (Matrix ι ι R) (Matrix ι ι R))).2 n
        (Matrix.entrywiseLinearMap f)
  have hGR :
      ((LinearMap.ker (Matrix.entrywiseLinearMap (ι := ι) f)).restrictScalars R).FG :=
    hG.restrictScalars
  let _ : Module.Finite R
      ((LinearMap.ker (Matrix.entrywiseLinearMap (ι := ι) f)).restrictScalars R) :=
    Module.Finite.of_fg hGR
  let _ : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_surjective (Matrix.kernelEntryLinearMap f j)
      (Matrix.kernelEntryLinearMap_surjective f j)
  exact Module.Finite.iff_fg.mp inferInstance

namespace Matrix

/-- A ring is left coherent if and only if its square matrix ring on a nonempty
finite index type is left coherent. -/
theorem isCoherentRing_iff [Nonempty ι] :
    IsCoherentRing (Matrix ι ι R) ↔ IsCoherentRing R := by
  constructor
  · intro h
    let _ : IsCoherentRing (Matrix ι ι R) := h
    exact IsCoherentRing.of_matrix (ι := ι)
  · intro h
    let _ : IsCoherentRing R := h
    infer_instance

end Matrix
