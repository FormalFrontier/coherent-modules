/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
Contributors: Anchor and other Formal Frontier AI agents
-/
module

public import CoherentModules.RingTheory.Ideal.AdicFinitePresentation

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
public import CoherentModules.LinearAlgebra.TensorProduct.Noetherian
public import CoherentModules.Localization
public import CoherentModules.ModuleCat
public import CoherentModules.RingTheory.Filtration
public import CoherentModules.RingTheory.Flat.BaseChange
public import CoherentModules.RingTheory.Flat.DirectSum
public import CoherentModules.RingTheory.Flat.Equiv
public import CoherentModules.RingTheory.Flat.FaithfullyFlat
public import CoherentModules.RingTheory.Flat.Localization
public import CoherentModules.RingTheory.Flat.TensorProduct
public import CoherentModules.RingTheory.Ideal.AdicCompatibility
public import CoherentModules.RingTheory.Ideal.AdicKrull
public import CoherentModules.RingTheory.Ideal.AdicLocality
public import CoherentModules.RingTheory.Ideal.Annihilator
public import CoherentModules.RingTheory.Ideal.FiniteModuleTransfer
public import CoherentModules.RingTheory.Ideal.Localization
public import CoherentModules.RingTheory.Ideal.Quotient.Annihilator
public import CoherentModules.RingTheory.Nakayama
public import CoherentModules.RingTheory.Noetherian
public import CoherentModules.RingTheory.Noetherian.Retraction
public import CoherentModules.TensorProduct
public import CoherentModules.UniversallyCoherent

/-!
# Coherent rings and modules

Public entry point for coherent modules, finite presentation, localization,
finite idealization, left Noetherianity of trivial square-zero extensions,
ideal-to-module transfer, Artin–Rees for Noetherian modules over arbitrary
commutative rings, finite-submodule adic cofinality with Noetherian-ring and
nilpotent-ideal providers, its Krull membership characterization and relative
annihilator separation and submodule intersection theorems,
left Noetherianity under unit clearing and additive right retractions,
the coherent-module category, universal coherence, Hom/tensor closure,
generator bounds for semilinear images, Noetherian scalar extension along
essentially finite-type algebras, and faithful flatness of tensor products
and direct sums. Flatness is invariant under compatible semilinear equivalences
of modules over equivalent commutative semirings, with mono-flatness understood
over semirings.
A direct sum of canonical principal localizations is faithfully flat exactly
when its generators span the unit ideal.
-/
