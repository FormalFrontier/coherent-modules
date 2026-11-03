/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Anchor and other Formal Frontier AI agents
-/
module

public import CoherentModules.Algebra.TrivSqZeroExt.Coherent
public import CoherentModules.LinearAlgebra.Matrix.TwoSidedIdeal

public import CoherentModules.RingTheory.Artinian.Hom

public import CoherentModules.LinearAlgebra.Dual.Coextension
public import CoherentModules.LinearAlgebra.Dual.End
public import CoherentModules.LinearAlgebra.Dual.Nondegenerate
public import CoherentModules.LinearAlgebra.Dual.TensorProduct
public import CoherentModules.LinearAlgebra.End.Local
public import CoherentModules.LinearAlgebra.End.StableKernelRange
public import CoherentModules.LinearAlgebra.Finsupp.LSum
public import CoherentModules.LinearAlgebra.FinsuppPi
public import CoherentModules.LinearAlgebra.KrullSchmidt
public import CoherentModules.LinearAlgebra.LinearMap.Exact
public import CoherentModules.LinearAlgebra.Matrix.ColumnHom
public import CoherentModules.LinearAlgebra.Matrix.Ideal
public import CoherentModules.LinearAlgebra.Matrix.Module
public import CoherentModules.LinearAlgebra.Matrix.Projective
public import CoherentModules.LinearAlgebra.Matrix.Reconstruction
public import CoherentModules.LinearAlgebra.Matrix.ReconstructionCoherence
public import CoherentModules.LinearAlgebra.Matrix.RowIdeal
public import CoherentModules.LinearAlgebra.Matrix.Submodule
public import CoherentModules.LinearAlgebra.Projective.Pure
public import CoherentModules.LinearAlgebra.Projective.RestrictScalars
public import CoherentModules.RingTheory.Ideal.AdicFinitePresentation

public import CoherentModules.Algebra.Category.ModuleCat.ChangeOfRings
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
public import CoherentModules.RingTheory.Artinian.Regular
public import CoherentModules.RingTheory.Filtration
public import CoherentModules.RingTheory.Finiteness.Pure
public import CoherentModules.RingTheory.Flat.BaseChange
public import CoherentModules.RingTheory.Flat.CategoryTheory
public import CoherentModules.RingTheory.Flat.DirectSum
public import CoherentModules.RingTheory.Flat.Equiv
public import CoherentModules.RingTheory.Flat.FaithfullyFlat
public import CoherentModules.RingTheory.Flat.FiniteWindows
public import CoherentModules.RingTheory.Flat.Localization
public import CoherentModules.RingTheory.Flat.Pure
public import CoherentModules.RingTheory.Flat.TensorProduct
public import CoherentModules.RingTheory.Ideal.AdicBaseChange
public import CoherentModules.RingTheory.Ideal.AdicCompatibility
public import CoherentModules.RingTheory.Ideal.AdicKrull
public import CoherentModules.RingTheory.Ideal.AdicLocality
public import CoherentModules.RingTheory.Ideal.AdicProducts
public import CoherentModules.RingTheory.Ideal.Annihilator
public import CoherentModules.RingTheory.Ideal.ModuleDetection
public import CoherentModules.RingTheory.Ideal.Comap
public import CoherentModules.RingTheory.Ideal.FiniteModuleTransfer
public import CoherentModules.RingTheory.Ideal.Localization
public import CoherentModules.RingTheory.Ideal.Maps
public import CoherentModules.RingTheory.Ideal.Operations
public import CoherentModules.RingTheory.Ideal.Quotient.Annihilator
public import CoherentModules.RingTheory.Ideal.TwoSided
public import CoherentModules.RingTheory.Morita.Matrix
public import CoherentModules.RingTheory.Nakayama
public import CoherentModules.RingTheory.Noetherian
public import CoherentModules.RingTheory.Noetherian.Retraction
public import CoherentModules.RingTheory.Pi
public import CoherentModules.RingTheory.Quotient
public import CoherentModules.RingTheory.TwoSidedIdeal.Atoms
public import CoherentModules.TensorProduct
public import CoherentModules.UniversallyCoherent

/-!
# Coherent rings and modules

Public entry point for coherent modules, finite presentation, localization,
coherence of finite dependent products over their product coefficient rings,
coherence of annihilator quotients under two commuting scalar actions,
finite idealization, left Noetherianity of trivial square-zero extensions,
ideal-to-module transfer, Artin–Rees for Noetherian modules over arbitrary
commutative rings, submodule adic cofinality with Noetherian-ring and
nilpotent-ideal providers and faithfully flat descent, its Krull membership
characterization and relative annihilator separation and submodule intersection
theorems,
left Noetherianity under unit clearing and additive right retractions,
units from left-regular elements in left Artinian rings, semimodule kernels,
annihilator preservation for finite semimodules under finite-limit-preserving
scalar extension, the coherent-module category, universal
coherence, Hom/tensor closure,
generator bounds for semilinear images, Noetherian scalar extension along
essentially finite-type algebras, and faithful flatness of tensor products
and direct sums. Flatness and faithful flatness of ring maps can be tested on
subring windows containing arbitrary finite subsets of the source and target.
Finite projectivity descends under injective tensor units along
central scalar extensions to possibly noncommutative semirings, without flatness
of the scalar algebra. Flatness is invariant under compatible semilinear equivalences
of modules over equivalent commutative semirings, with mono-flatness understood
over semirings.
Extension of left ideals along a unital semiring homomorphism preserves products
when the extension of the first factor is two-sided, and preserves all powers
when the extended ideal is two-sided.
Relative generation bounds persist along every power of a left ideal over a
semiring; a globally nilpotent ideal cannot enlarge relative generation.
Dualization is an algebra homomorphism from the opposite endomorphism algebra;
composing with left multiplication gives named right-translation operators on the dual.
Coextension along the opposite algebra, restricted to the base, is linearly equivalent
to the original dual and intertwines its translation with these named operators.
A surjective self-pairing that separates the left slot is nondegenerate in both slots.
For finite nonempty indices, coordinatewise extension is an additive Hom equivalence
and an endomorphism semiring equivalence for matrix columns over arbitrary semirings;
for empty indices it remains surjective.
Simultaneous one-step stability of the kernel and range of a module endomorphism
gives a canonical nilpotent/invertible sum decomposition over semiring scalars
on an additive commutative group, natural for arbitrary linear intertwiners.
Over arbitrary ring scalars, an indecomposable finite-length module has a local
endomorphism ring, and each endomorphism is nilpotent or a unit. Noetherian or
Artinian modules separately admit finite internal decompositions into nonzero
indecomposable submodules. Supplied finite internal decompositions with local
endomorphism rings match up to reindexing and linear equivalence, and a common
finite-length module cancels from a product with arbitrary remaining factors.
A direct sum of canonical principal localizations is faithfully flat exactly
when its generators span the unit ideal. The two-sided ideal lattice of any
unital, possibly nonassociative ring is coatomic.
-/
