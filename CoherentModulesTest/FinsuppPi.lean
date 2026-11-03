/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

import CoherentModules.LinearAlgebra.FinsuppPi

/-! A two-coordinate calculation with varying natural scalars and an infinite degree type. -/

example :
    (Finsupp.piLinearEquiv (fun _ : Bool => ℕ) (fun _ : Bool => ℕ)
      ((fun b : Bool => if b then 3 else 2) •
        Finsupp.single (7 : ℕ) (fun b : Bool => if b then 7 else 5)) false,
     Finsupp.piLinearEquiv (fun _ : Bool => ℕ) (fun _ : Bool => ℕ)
      ((fun b : Bool => if b then 3 else 2) •
        Finsupp.single (7 : ℕ) (fun b : Bool => if b then 7 else 5)) true) =
      (Finsupp.single 7 10, Finsupp.single 7 21) := by
  simp
