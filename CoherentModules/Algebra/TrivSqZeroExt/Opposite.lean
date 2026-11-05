/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Ring.Equiv

/-!
# Opposites of trivial square-zero extensions

The opposite of `TrivSqZeroExt R M` is additively and multiplicatively equivalent to
`TrivSqZeroExt Rᵐᵒᵖ M` with the two scalar actions exchanged. The equivalence sends
`op (r, m)` to `(op r, m)`. The target left action is the given right action, and the
target right action is the given left action pulled back along double `unop`.
The inverse function, accessed through `EquivLike.inv`, sends `(a, m)` to
`op (unop a, m)`.

Only addition and multiplication on `R`, commutative addition on `M`, and the two
scalar actions are needed. Associativity, zero, and compatibility between the actions
are not required for the equivalence. The inclusion formulas require only the zero
structures used by the corresponding inclusions.

This construction uses Mathlib's trivial square-zero extensions, formalized by
Kenny Lau, Eric Wieser, Antoine Chambert-Loir and María-Inés de Frutos-Fernández,
and Mathlib's opposite and action-pullback infrastructure.
-/

@[expose] public section

universe u v

namespace TrivSqZeroExt

open MulOpposite

variable {R : Type u} {M : Type v} [Add R] [Mul R] [AddCommMagma M]
  [leftAction : SMul R M] [rightAction : SMul Rᵐᵒᵖ M]

/-- The opposite of a trivial square-zero extension, with the scalar actions exchanged.

The target multiplication uses the original right action as its left action. Its right
action is the original left action pulled back by `q ↦ unop (unop q)`, rather than an
additional scalar action on `M`. -/
def opEquiv :
    @RingEquiv (TrivSqZeroExt R M)ᵐᵒᵖ (TrivSqZeroExt Rᵐᵒᵖ M)
      inferInstance
      (@TrivSqZeroExt.mul Rᵐᵒᵖ M inferInstance inferInstance rightAction
        (SMul.comp M (fun q : Rᵐᵒᵖᵐᵒᵖ => unop (unop q))))
      inferInstance
      (@TrivSqZeroExt.add Rᵐᵒᵖ M inferInstance inferInstance) := by
  let _ : SMul Rᵐᵒᵖᵐᵒᵖ M :=
    SMul.comp M (fun q : Rᵐᵒᵖᵐᵒᵖ => unop (unop q))
  exact
    { toFun x := (op (unop x).fst, (unop x).snd)
      invFun x := op (unop x.fst, x.snd)
      left_inv _ := rfl
      right_inv _ := rfl
      map_mul' _ _ := TrivSqZeroExt.ext rfl (add_comm _ _)
      map_add' _ _ := rfl }

/-- The coordinate formula for the opposite equivalence. -/
theorem opEquiv_apply (x : (TrivSqZeroExt R M)ᵐᵒᵖ) :
    opEquiv (R := R) (M := M) x = (op (unop x).fst, (unop x).snd) :=
  rfl

/-- The coordinate formula for the inverse opposite equivalence. -/
theorem opEquiv_symm_apply (x : TrivSqZeroExt Rᵐᵒᵖ M) :
    EquivLike.inv (opEquiv (R := R) (M := M)) x = op (unop x.fst, x.snd) :=
  rfl

@[simp]
theorem opEquiv_apply_fst (x : (TrivSqZeroExt R M)ᵐᵒᵖ) :
    (opEquiv (R := R) (M := M) x).fst = op (unop x).fst :=
  rfl

@[simp]
theorem opEquiv_apply_snd (x : (TrivSqZeroExt R M)ᵐᵒᵖ) :
    (opEquiv (R := R) (M := M) x).snd = (unop x).snd :=
  rfl

@[simp]
theorem opEquiv_symm_apply_fst (x : TrivSqZeroExt Rᵐᵒᵖ M) :
    (unop ((@RingEquiv.symm _ _ _
      (@TrivSqZeroExt.mul Rᵐᵒᵖ M inferInstance inferInstance rightAction
        (SMul.comp M (fun q : Rᵐᵒᵖᵐᵒᵖ => unop (unop q)))) _ _
      (opEquiv (R := R) (M := M))) x)).fst = unop x.fst :=
  rfl

@[simp]
theorem opEquiv_symm_apply_snd (x : TrivSqZeroExt Rᵐᵒᵖ M) :
    (unop ((@RingEquiv.symm _ _ _
      (@TrivSqZeroExt.mul Rᵐᵒᵖ M inferInstance inferInstance rightAction
        (SMul.comp M (fun q : Rᵐᵒᵖᵐᵒᵖ => unop (unop q)))) _ _
      (opEquiv (R := R) (M := M))) x)).snd = x.snd :=
  rfl

@[simp]
theorem opEquiv_inl [Zero M] (r : R) :
    opEquiv (R := R) (M := M) (op (inl r)) = inl (op r) :=
  rfl

@[simp]
theorem opEquiv_inr [Zero R] (m : M) :
    opEquiv (R := R) (M := M) (op (inr m)) = inr m :=
  rfl

@[simp]
theorem opEquiv_symm_inl [Zero M] (r : Rᵐᵒᵖ) :
    EquivLike.inv (opEquiv (R := R) (M := M)) (inl r) = op (inl (unop r)) :=
  rfl

@[simp]
theorem opEquiv_symm_inr [Zero R] (m : M) :
    EquivLike.inv (opEquiv (R := R) (M := M)) (inr m) = op (inr m) :=
  rfl

end TrivSqZeroExt
