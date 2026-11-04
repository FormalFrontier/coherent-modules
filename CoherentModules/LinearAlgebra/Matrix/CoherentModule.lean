/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.Basic
public import Mathlib.LinearAlgebra.Matrix.Module

/-!
# Coherence of matrix-column modules

For a ring `R`, an additive commutative monoid `M` with its given `R`-module
structure, and a finite type `ι` with decidable equality, the column action is
`(A • v) i = ∑ j, A i j • v j`. Coherence of `M` implies coherence of this
`Matrix ι ι R`-module, including when `ι` is empty. For nonempty `ι`, the
converse holds as well.

The statements use `Matrix.Module.matrixModule`. The additive group needed by
this constructor is obtained from the given coefficient action using
`Module.addCommMonoidToAddCommGroup`; the original addition, natural multiples,
and coefficient module structure are unchanged. Neither commutativity nor
nontriviality of `R` is required.

## Main declarations

* `Matrix.Module.instIsCoherent`: preservation of coherence by finite columns.
* `Module.IsCoherent.of_matrixModule`: reflection for nonempty finite columns.
* `Matrix.Module.isCoherent_iff`: the resulting nonempty-index equivalence.

Reflection uses coordinatewise extension of a coefficient-linear map from a
finite-rank free module. Its range is finitely presented by column coherence,
so its kernel is finitely generated. Restriction of scalars and a coordinate
projection then give finite generation of the coefficient kernel. This does
not require coherence of the coefficient ring.

## References

The column action and coordinatewise lift are Mathlib's
`Matrix.Module.matrixModule` and `LinearMap.mapMatrixModule` (Yunzhou Xie).
The proof uses the coherent-module kernel criterion and scalar-ascent theorem
from `CoherentModules.Basic`, together with Mathlib's finite-presentation and
finite-generation APIs.
-/

universe uR uI uM uP

namespace Matrix

section ScalarTower

variable {R : Type uR} {ι : Type uI} {P : Type uP}
variable [r : Ring R] [hι : Fintype ι] [dι : DecidableEq ι]
variable [gP : AddCommGroup P] [mP : Module R P]

local notation "columnModule" => (@Matrix.Module.matrixModule ι R P r hι dι gP mP)
local notation "pointwiseModule" =>
  (@Pi.module ι (fun _ => P) R r.toSemiring
    (fun _ => gP.toAddCommMonoid) (fun _ => mP))

-- Specify all three actions: coefficientwise multiplication on matrices,
-- the column action, and the original pointwise coefficient action.
open scoped Matrix.Module in
private theorem columnScalarTower :
    @IsScalarTower R (Matrix ι ι R) (ι → P)
      (inferInstance : SMul R (Matrix ι ι R))
      (columnModule).toDistribMulAction.toMulAction.toSemigroupAction.toSMul
      (pointwiseModule).toDistribMulAction.toMulAction.toSemigroupAction.toSMul :=
  inferInstance

end ScalarTower

section Kernel

variable {R : Type uR} {ι : Type uI} {P : Type uP} {M : Type uM}
variable [r : Ring R] [hι : Fintype ι] [dι : DecidableEq ι]
variable [gP : AddCommGroup P] [mP : Module R P]
variable [aM : AddCommMonoid M] [mM : Module R M]

/-- The source column action retains its given coefficient group and module. -/
local instance sourceColumnModule : Module (Matrix ι ι R) (ι → P) :=
  @Matrix.Module.matrixModule ι R P r hι dι gP mP

/-- The target column action uses inverses induced by its coefficient action. -/
local instance targetColumnModule : Module (Matrix ι ι R) (ι → M) :=
  @Matrix.Module.matrixModule ι R M r hι dι
    (Module.addCommMonoidToAddCommGroup R (M := M)) mM

local instance : IsScalarTower R (Matrix ι ι R) (ι → P) :=
  columnScalarTower

local instance : IsScalarTower R (Matrix ι ι R) (ι → M) := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R (M := M)
  exact columnScalarTower

local notation "columnMap" f =>
  (@LinearMap.mapMatrixModule ι R P M r hι dι gP mP
    (Module.addCommMonoidToAddCommGroup R (M := M)) mM f)

private theorem ker_columnMap_restrictScalars (f : P →ₗ[R] M) :
    (LinearMap.ker (columnMap f)).restrictScalars R =
      Submodule.pi Set.univ (fun _ : ι => LinearMap.ker f) := by
  have hmap : (columnMap f).restrictScalars R = f.compLeft ι := by
    ext v i
    rfl
  rw [← LinearMap.ker_restrictScalars R, hmap, LinearMap.ker_compLeft]

end Kernel

end Matrix

@[expose] public section

variable {R : Type uR} {ι : Type uI} {M : Type uM}
variable [r : Ring R] [hι : Fintype ι] [dι : DecidableEq ι]
variable [aM : AddCommMonoid M] [mM : Module R M]

/-- Finite matrix columns over a coherent module are coherent for the column
action. The finite index type may be empty. -/
instance Matrix.Module.instIsCoherent [Module.IsCoherent R M] :
    @Module.IsCoherent (Matrix ι ι R)
      (inferInstance : Ring (Matrix ι ι R)) (ι → M)
      (@Pi.addCommMonoid ι (fun _ => M) (fun _ => aM))
      (@Matrix.Module.matrixModule ι R M r hι dι
        (Module.addCommMonoidToAddCommGroup R (M := M)) mM) := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R (M := M)
  let : Module (Matrix ι ι R) (ι → M) :=
    @Matrix.Module.matrixModule ι R M r hι dι ‹AddCommGroup M› mM
  let : IsScalarTower R (Matrix ι ι R) (ι → M) := Matrix.columnScalarTower
  let : Module.Finite R (Matrix ι ι R) :=
    inferInstanceAs (Module.Finite R (ι → ι → R))
  let : Module.IsCoherent R (ι → M) := Module.IsCoherent.pi
  exact Module.IsCoherent.of_restrictScalars R

/-- Coherence of a matrix-column module on a nonempty finite index type implies
coherence of the original coefficient module. -/
theorem Module.IsCoherent.of_matrixModule [Nonempty ι]
    (h : @Module.IsCoherent (Matrix ι ι R)
      (inferInstance : Ring (Matrix ι ι R)) (ι → M)
      (@Pi.addCommMonoid ι (fun _ => M) (fun _ => aM))
      (@Matrix.Module.matrixModule ι R M r hι dι
        (Module.addCommMonoidToAddCommGroup R (M := M)) mM)) :
    Module.IsCoherent R M := by
  obtain ⟨j⟩ := ‹Nonempty ι›
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup R (M := M)
  let : Module (Matrix ι ι R) (ι → M) :=
    @Matrix.Module.matrixModule ι R M r hι dι ‹AddCommGroup M› mM
  let : IsScalarTower R (Matrix ι ι R) (ι → M) := Matrix.columnScalarTower
  let : Module.Finite R (Matrix ι ι R) :=
    inferInstanceAs (Module.Finite R (ι → ι → R))
  let : Module.IsCoherent (Matrix ι ι R) (ι → M) := h
  -- Finite generation is a separate part of the coherent-module criterion.
  let : Module.Finite R (ι → M) := Module.Finite.trans (Matrix ι ι R) (ι → M)
  let : Module.Finite R M :=
    Module.Finite.of_surjective (LinearMap.proj j : (ι → M) →ₗ[R] M)
      (LinearMap.proj_surjective j)
  apply Module.IsCoherent.iff_finite_and_fg_ker.mpr
  refine ⟨inferInstance, ?_⟩
  intro n f
  -- The free coefficient source keeps its original Pi group and R-action.
  let : Module (Matrix ι ι R) (ι → (Fin n → R)) :=
    @Matrix.Module.matrixModule ι R (Fin n → R) r hι dι
      (inferInstance : AddCommGroup (Fin n → R)) (inferInstance : Module R (Fin n → R))
  let : IsScalarTower R (Matrix ι ι R) (ι → (Fin n → R)) := Matrix.columnScalarTower
  let : Module.Finite (Matrix ι ι R) (ι → (Fin n → R)) :=
    Module.Finite.of_restrictScalars_finite R (Matrix ι ι R) (ι → (Fin n → R))
  let G : (ι → (Fin n → R)) →ₗ[Matrix ι ι R] (ι → M) :=
    @LinearMap.mapMatrixModule ι R (Fin n → R) M r hι dι
      (inferInstance : AddCommGroup (Fin n → R)) (inferInstance : Module R (Fin n → R))
      (Module.addCommMonoidToAddCommGroup R (M := M)) mM f
  let : Module.FinitePresentation (Matrix ι ι R) (LinearMap.range G) :=
    Module.IsCoherent.finitePresentation_submodule _ (Submodule.fg_range G)
  have hK : (LinearMap.ker G).FG := by
    simpa only [LinearMap.ker_rangeRestrict] using
      Module.FinitePresentation.fg_ker G.rangeRestrict (LinearMap.surjective_rangeRestrict G)
  have hKR : ((LinearMap.ker G).restrictScalars R).FG := hK.restrictScalars
  rw [Matrix.ker_columnMap_restrictScalars (ι := ι) f] at hKR
  have hproj :
      (Submodule.pi Set.univ (fun _ : ι => LinearMap.ker f)).map
          (LinearMap.proj j : (ι → (Fin n → R)) →ₗ[R] (Fin n → R)) =
        LinearMap.ker f := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (Submodule.mem_pi.mp hv) j (Set.mem_univ j)
    · intro hx
      refine ⟨fun _ => x, ?_, rfl⟩
      exact Submodule.mem_pi.mpr fun _ _ => hx
  rw [← hproj]
  exact hKR.map _

/-- For nonempty finite indices, coherence of the matrix-column module is
equivalent to coherence of the coefficient module. Empty indices are excluded:
their column module is a subsingleton for every coefficient module. -/
theorem Matrix.Module.isCoherent_iff [Nonempty ι] :
    @Module.IsCoherent (Matrix ι ι R)
      (inferInstance : Ring (Matrix ι ι R)) (ι → M)
      (@Pi.addCommMonoid ι (fun _ => M) (fun _ => aM))
      (@Matrix.Module.matrixModule ι R M r hι dι
        (Module.addCommMonoidToAddCommGroup R (M := M)) mM) ↔
      Module.IsCoherent R M := by
  constructor
  · exact Module.IsCoherent.of_matrixModule
  · intro h
    let : Module.IsCoherent R M := h
    exact Matrix.Module.instIsCoherent
