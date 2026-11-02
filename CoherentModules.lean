/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Anchor and other Formal Frontier AI agents
-/
module

public import CoherentModules.RingTheory.Ideal.AdicFinitePresentation

public import CoherentModules.Algebra.Category.ModuleCat.Kernels
public import CoherentModules.Algebra.Category.ModuleCat.Monoidal.Closed
public import CoherentModules.Algebra.Module.Coprime
public import CoherentModules.Algebra.Module.SpanRank
public import CoherentModules.Algebra.TrivSqZeroExt.Finite
public import CoherentModules.Algebra.TrivSqZeroExt.Noetherian
public import CoherentModules.Basic
public import CoherentModules.FinitePresentation
public import CoherentModules.Hom
public import CoherentModules.LinearAlgebra.TensorProduct.Annihilator
public import CoherentModules.LinearAlgebra.TensorProduct.FiniteDetection
public import CoherentModules.LinearAlgebra.TensorProduct.FiniteSurjectivity
public import CoherentModules.LinearAlgebra.TensorProduct.Generation
public import CoherentModules.LinearAlgebra.TensorProduct.Kernel
public import CoherentModules.LinearAlgebra.TensorProduct.Noetherian
public import CoherentModules.Localization
public import CoherentModules.ModuleCat
public import CoherentModules.RingTheory.Filtration
public import CoherentModules.RingTheory.Flat.BaseChange
public import CoherentModules.RingTheory.Flat.CategoryTheory
public import CoherentModules.RingTheory.Flat.DirectSum
public import CoherentModules.RingTheory.Flat.Equiv
public import CoherentModules.RingTheory.Flat.FaithfullyFlat
public import CoherentModules.RingTheory.Flat.Localization
public import CoherentModules.RingTheory.Flat.TensorProduct
public import CoherentModules.RingTheory.Ideal.AdicBaseChange
public import CoherentModules.RingTheory.Ideal.AdicCompatibility
public import CoherentModules.RingTheory.Ideal.AdicKrull
public import CoherentModules.RingTheory.Ideal.AdicLocality
public import CoherentModules.RingTheory.Ideal.AdicProducts
public import CoherentModules.RingTheory.Ideal.Annihilator
public import CoherentModules.RingTheory.Ideal.FiniteModuleTransfer
public import CoherentModules.RingTheory.Ideal.Localization
public import CoherentModules.RingTheory.Ideal.Maps
public import CoherentModules.RingTheory.Ideal.Operations
public import CoherentModules.RingTheory.Ideal.Quotient.Annihilator
public import CoherentModules.RingTheory.Nakayama
public import CoherentModules.RingTheory.Noetherian
public import CoherentModules.RingTheory.Noetherian.Retraction
public import CoherentModules.RingTheory.TwoSidedIdeal.Atoms
public import CoherentModules.TensorProduct
public import CoherentModules.UniversallyCoherent

/-!
# Coherent rings and modules

Public entry point for coherent modules, finite presentation, localization,
finite idealization, left Noetherianity of trivial square-zero extensions,
ideal-to-module transfer, Artin–Rees for Noetherian modules over arbitrary
commutative rings, submodule adic cofinality with Noetherian-ring and
nilpotent-ideal providers and faithfully flat descent, its Krull membership
characterization and relative annihilator separation and submodule intersection
theorems,
left Noetherianity under unit clearing and additive right retractions,
semimodule kernels, annihilator preservation for finite semimodules under
finite-limit-preserving scalar extension, the coherent-module category, universal
coherence, Hom/tensor closure,
generator bounds for semilinear images, Noetherian scalar extension along
essentially finite-type algebras, and faithful flatness of tensor products
and direct sums. Flatness is invariant under compatible semilinear equivalences
of modules over equivalent commutative semirings, with mono-flatness understood
over semirings.
Extension of left ideals along a unital semiring homomorphism preserves products
when the extension of the first factor is two-sided, and preserves all powers
when the extended ideal is two-sided.
Relative generation bounds persist along every power of a left ideal over a
semiring; a globally nilpotent ideal cannot enlarge relative generation.
A direct sum of canonical principal localizations is faithfully flat exactly
when its generators span the unit ideal. The two-sided ideal lattice of any
unital, possibly nonassociative ring is coatomic.
-/
