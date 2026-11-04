/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Data.Matrix.Basis

/-!
# Entrywise linear maps on regular matrix modules

A coefficient-linear map `f : (κ → R) →ₗ[R] R` induces a map on families of finite
square matrices by applying `f` to each entry. This lift is linear for the regular
left matrix action, even when the coefficient semiring is noncommutative and the
family index `κ` is infinite.

## Main declarations

* `Matrix.entrywiseLinearMap`: the regular matrix-linear entrywise lift.
* `Matrix.entrywiseLinearMap_eq_mapMatrix`: compatibility with Mathlib's
  coefficient-linear `LinearMap.mapMatrix` after rearranging coordinates.
* `Matrix.kernelEntryLinearMap`: a coefficient-linear entry projection from the
  scalar-restricted kernel of the lift.
* `Matrix.kernelSingleLinearMap`: its single-entry section, with split identity
  and surjectivity of the projection.
* `Matrix.entrywiseLinearMap_mulRight_apply`: lifting coefficient right multiplication
  is right multiplication by the corresponding scalar matrix.

## Implementation notes

All actions are the given canonical ones: the matrix action is regular left
multiplication, and the coefficient action on matrices is entrywise. No column-action
instance is opened. The proof of matrix-linearity distributes a finite sum of left
coefficient multiples; it does not commute coefficient factors.

## References

The constructions use Mathlib's matrix, coordinate-linear-map and scalar-restriction
APIs. The comparison with `LinearMap.mapMatrix` distinguishes coefficient-linearity
on matrices of coefficient families from regular matrix-linearity on families of matrices.
-/

@[expose] public section

universe uR uI uK

namespace Matrix

variable {R : Type uR} {ι : Type uI} {κ : Type uK}
variable [Semiring R] [Fintype ι] [DecidableEq ι]

/-- Apply a coefficient-linear map entrywise to a family of matrices. Both matrix modules
have their regular left action. No finiteness assumption on the family index is needed. -/
def entrywiseLinearMap (f : (κ → R) →ₗ[R] R) :
    (κ → Matrix ι ι R) →ₗ[Matrix ι ι R] Matrix ι ι R where
  toFun A := Matrix.of fun a b => f (fun k => A k a b)
  map_add' A C := by
    ext a b
    exact f.map_add (fun k => A k a b) (fun k => C k a b)
  map_smul' B A := by
    ext a b
    change f (fun k => (B * A k) a b) =
      (B * Matrix.of (fun c d => f (fun k => A k c d))) a b
    simp only [Matrix.mul_apply, Matrix.of_apply]
    calc
      f (fun k => ∑ c, B a c * A k c b) =
          f (∑ c, B a c • (fun k => A k c b)) := by
        congr 1
        funext k
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      _ = ∑ c, B a c * f (fun k => A k c b) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro c _
        exact f.map_smul (B a c) (fun k => A k c b)

/-- Entries of the regular matrix-linear lift. -/
@[simp]
theorem entrywiseLinearMap_apply (f : (κ → R) →ₗ[R] R)
    (A : κ → Matrix ι ι R) (a b : ι) :
    entrywiseLinearMap f A a b = f (fun k => A k a b) :=
  rfl

/-- After rearranging the family and matrix coordinates, the regular matrix-linear lift
agrees pointwise with Mathlib's coefficient-linear map on matrices. -/
theorem entrywiseLinearMap_eq_mapMatrix (f : (κ → R) →ₗ[R] R)
    (A : κ → Matrix ι ι R) :
    entrywiseLinearMap f A = f.mapMatrix (Matrix.of fun a b k => A k a b) :=
  rfl

/-- Entry projection from the scalar-restricted kernel of the entrywise lift to the
coefficient kernel. It uses the pointwise coefficient action on matrices. -/
def kernelEntryLinearMap (f : (κ → R) →ₗ[R] R) (j : ι) :
    ((LinearMap.ker (entrywiseLinearMap (ι := ι) f)).restrictScalars R) →ₗ[R]
      LinearMap.ker f :=
  (((Matrix.entryLinearMap R R j j).compLeft κ).domRestrict
    ((LinearMap.ker (entrywiseLinearMap (ι := ι) f)).restrictScalars R)).codRestrict
      (LinearMap.ker f) (by
        intro A
        apply LinearMap.mem_ker.mpr
        have hA : entrywiseLinearMap f A.val = 0 := LinearMap.mem_ker.mp A.property
        exact congrArg (fun M : Matrix ι ι R => M j j) hA)

/-- Coordinates of the kernel entry projection. -/
@[simp]
theorem kernelEntryLinearMap_apply (f : (κ → R) →ₗ[R] R) (j : ι)
    (A : (LinearMap.ker (entrywiseLinearMap (ι := ι) f)).restrictScalars R) (k : κ) :
    (kernelEntryLinearMap f j A).val k = A.val k j j :=
  rfl

/-- Place a coefficient-kernel vector in one diagonal entry of every matrix in the family.
This is a coefficient-linear section of `Matrix.kernelEntryLinearMap`. -/
def kernelSingleLinearMap (f : (κ → R) →ₗ[R] R) (j : ι) :
    LinearMap.ker f →ₗ[R]
      ((LinearMap.ker (entrywiseLinearMap (ι := ι) f)).restrictScalars R) :=
  (((Matrix.singleLinearMap R j j).compLeft κ).domRestrict (LinearMap.ker f)).codRestrict
    ((LinearMap.ker (entrywiseLinearMap (ι := ι) f)).restrictScalars R) (by
      intro x
      change entrywiseLinearMap f (fun k => Matrix.single j j (x.val k)) = 0
      ext a b
      change f (fun k => Matrix.single j j (x.val k) a b) = 0
      by_cases ha : j = a
      · subst a
        by_cases hb : j = b
        · subst b
          simpa only [Matrix.single_apply_same] using LinearMap.mem_ker.mp x.property
        · have hz : (fun k => Matrix.single j j (x.val k) j b) = (0 : κ → R) := by
            funext k
            simp [hb]
          rw [hz]
          exact f.map_zero
      · have hz : (fun k => Matrix.single j j (x.val k) a b) = (0 : κ → R) := by
          funext k
          simp [ha]
        rw [hz]
        exact f.map_zero)

/-- Matrices in the kernel single-entry section. -/
@[simp]
theorem kernelSingleLinearMap_apply (f : (κ → R) →ₗ[R] R) (j : ι)
    (x : LinearMap.ker f) (k : κ) :
    (kernelSingleLinearMap f j x).val k = Matrix.single j j (x.val k) :=
  rfl

/-- The kernel entry projection composed with its single-entry section is the identity. -/
@[simp]
theorem kernelEntryLinearMap_comp_kernelSingleLinearMap (f : (κ → R) →ₗ[R] R) (j : ι) :
    (kernelEntryLinearMap f j).comp (kernelSingleLinearMap f j) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  funext k
  simp only [LinearMap.comp_apply, LinearMap.id_apply, kernelEntryLinearMap_apply,
    kernelSingleLinearMap_apply, Matrix.single_apply_same]

/-- Every coefficient-kernel vector is the diagonal entry of a vector in the lifted kernel. -/
theorem kernelEntryLinearMap_surjective (f : (κ → R) →ₗ[R] R) (j : ι) :
    Function.Surjective (kernelEntryLinearMap f j) := by
  intro x
  refine ⟨kernelSingleLinearMap f j x, ?_⟩
  exact congrArg (fun h : LinearMap.ker f →ₗ[R] LinearMap.ker f => h x)
    (kernelEntryLinearMap_comp_kernelSingleLinearMap f j)

/-- Lifting right multiplication after a coordinate projection multiplies a matrix on the
right by the scalar matrix. No centrality of the coefficient is assumed. -/
theorem entrywiseLinearMap_mulRight_apply (a : R) (k : κ) (A : κ → Matrix ι ι R) :
    entrywiseLinearMap ((LinearMap.mulRight R a).comp (LinearMap.proj k)) A =
      A k * Matrix.scalar ι a := by
  ext i j
  simp only [entrywiseLinearMap_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
    LinearMap.proj_apply, Matrix.scalar_apply, Matrix.mul_diagonal]

end Matrix
