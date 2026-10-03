# Using coherent modules

Import `CoherentModules` for the complete library, or one of the nine leaves in
the table below. Its only mathematical dependency is the pinned mathlib. The
[historical generated API](API.md) covers the original seven leaves; follow the
source links below for the square-zero and ideal/module declarations. The Lean
statements are authoritative about hypotheses and universes.

| Leaf | Purpose and important boundary |
| --- | --- |
| `CoherentModules.Basic` | Coherent modules/rings over an arbitrary `Ring`; finite generation and finite presentation of finitely generated submodules. |
| `CoherentModules.FinitePresentation` | Over a coherent ring, coherence iff finite presentation; exact-five finite-presentation criterion. |
| `CoherentModules.Localization` | Preservation and spanning-family descent over a `CommRing`, for arbitrary localization realizations. |
| `CoherentModules.ModuleCat` | The coherent-object property and transparent abelian full subcategory of `ModuleCat`. |
| `CoherentModules.Hom` | Hom closure over a `CommRing`, with finitely presented source and coherent target. |
| `CoherentModules.TensorProduct` | Tensor closure over a `CommRing`, with finitely presented first factor and coherent second factor. |
| `CoherentModules.UniversallyCoherent` | Coherence of every finitely presented commutative algebra in a specified target universe. |
| [`CoherentModules.Algebra.TrivSqZeroExt.Finite`](../CoherentModules/Algebra/TrivSqZeroExt/Finite.lean) | Projection-kernel equivalence, whole-extension kernel finiteness and projection base change over a commutative semiring. |
| [`CoherentModules.RingTheory.Ideal.FiniteModuleTransfer`](../CoherentModules/RingTheory/Ideal/FiniteModuleTransfer.lean) | Transfer of isomorphism-invariant, square-zero-descent-stable properties from finite ideals to finite modules over finite-type algebras. |

## Foundation and finite presentation

`Module.IsCoherent R M` packages finite generation of `M` and finite presentation
of every finitely generated submodule. In particular, it gives finite presentation
of `M`. Its finite-free characterization asks for finite generation of kernels of
maps from finite-rank free modules to `M`; the zero-rank case is included.
`IsCoherentRing R` is coherence of `R` as its own module, not a Noetherian condition.

The closure theorems cover finitely generated submodules, linear equivalences,
finite products, kernels between coherent modules, quotients by finitely generated
submodules, cokernels and extensions. They do not assert that every submodule or
every quotient of a coherent module is coherent without the stated finiteness.

Over a coherent ring, finite presentation and coherence are equivalent, so a
kernel between finitely presented modules is finitely presented. The exact-five
criterion concerns `M₁ → M₂ → M₃ → M₄ → M₅`: exactness is required at the three
middle modules; `M₁` is finite and `M₂`, `M₄`, `M₅` are finitely presented. It
concludes finite presentation of `M₃` without endpoint injectivity/surjectivity.

## Localization, Hom and tensor

`Module.IsCoherent.of_isLocalizedModule` uses the ring and module localization
universal properties; it does not require a surjective localization map. The
canonical localization instance and `away` theorem specialize it. Descent uses
localization away from elements of a set whose ideal span is the unit ideal,
including arbitrary realizations in `of_localizationSpan'`.

For `[CommRing R]`, `[Module.FinitePresentation R M]` and
`[Module.IsCoherent R N]`, use `Module.IsCoherent.linearMap` for `M →ₗ[R] N` and
`Module.IsCoherent.tensorProduct` for `M ⊗[R] N`. These are theorems, not global
instances; they require neither a coherent nor a Noetherian base ring. The two
module carrier universes are independent. The tracked
[Hom](../CoherentModulesTest/Hom.lean) and
[tensor](../CoherentModulesTest/TensorProduct.lean) clients demonstrate the exact
applications, including zero/subsingleton boundaries.

## Categories and universal coherence

`ModuleCat.isCoherent` tests coherence of the underlying module. Its closure under
isomorphisms, zero objects, finite products, kernels and cokernels supplies the
generic abelian structure on `CoherentModuleCat R`. The latter remains a transparent
full-subcategory abbreviation; this assembly does not replace its definitional
API or impose a coherent-ring hypothesis. The
[category clients](../CoherentModulesTest/ModuleCat.lean) include reduction checks.

`IsUniversallyCoherent.{u, v} R` quantifies over finitely presented commutative
algebras in `Type v` while `R : Type u`. The target universe is deliberately
independent. Base-ring coherence uses the specialization `v = u`; the algebra-
equivalence theorem transports coherence between suitably equivalent algebras.
The Noetherian instance supplies universal coherence. No nonzero-ring or
nonempty-basis assumption is added.

## Square-zero extensions and finite modules

For `[CommSemiring R] [AddCommMonoid M] [Module R M]`, the projection kernel of
`TrivSqZeroExt R M` is `R`-linearly equivalent to `M` via
[`TrivSqZeroExt.kerIdealLinearEquiv`](../CoherentModules/Algebra/TrivSqZeroExt/Finite.lean).
The `kerIdealLinearEquiv_apply` and `kerIdealLinearEquiv_symm_apply` simp lemmas
describe its second-coordinate map and inverse `inr`. If `[Module.Finite R M]`,
`TrivSqZeroExt.kerIdeal_finite` makes the kernel finite **as a module over the
whole extension**, not only over `R`. The semiring-level
`TrivSqZeroExt.kerIdealBaseChange` identifies
`R ⊗[TrivSqZeroExt R M] TrivSqZeroExt.kerIdeal R M` with `M` even if `M` is not
finite. Its `kerIdealBaseChange_tmul` and `kerIdealBaseChange_symm_apply` simp
rules specify the pure-tensor and inverse values. Use `open scoped TrivSqZeroExt`
for the canonical opposite action and central scalar structure; the projection
algebra remains local to the construction.

For `[CommRing A]`,
[`Ideal.ideal_property_iff_module_property`](../CoherentModules/RingTheory/Ideal/FiniteModuleTransfer.lean)
tests a predicate on finite modules over finite-type `A`-algebras via finitely
generated ideals. The predicate must be invariant under compatible algebra and
finite-module isomorphisms and descend along **every** compatible surjective
square-zero algebra map for a finite source module. The base `A : Type uA` may
have a different universe from the common universe of algebra carriers and
their modules. Neither an algebra finite as an `A`-module nor a projective or
coherent module is assumed. The
[client examples](../CoherentModulesTest/Algebra/TrivSqZeroExt/Finite.lean) use
`ZMod 2` for finite nonfree torsion and `ZMod 1` for the zero case, demonstrate
projection base change over `ℕ`, and independently establish the predicate's
isomorphism and descent hypotheses before applying transfer.

## Checks, cost and limits

The default Lake targets include the aggregate and all ten `CoherentModulesTest`
modules. Stable private test declarations exercise hypotheses, independent
universes and degenerate cases without creating another exported API. The
historical public axiom list is intentionally not a private/generated proof census.
A complete transitive audit of *actual* declarations,
including private and generated ones, is a separate acceptance condition; ordinary
builds check proofs, without a mandatory separate stored-body replay.

### Build and audit resource baseline

The historical first-release baseline below was measured on September 25, 2026, using
Lean `v4.34.0-rc2` (compiler `6a10ac8c22beadecabdbb0919c2b50214762f91d`),
mathlib `83abb3e776bdefcbc447a1e44d0debe4010039e5` and the nine-package
`lake-manifest.json`. At the original measurement, all 17 Lean files and three
Lean/Lake inputs matched source revision `91e1a1e8881ef55c045b3a5eb5285875be21a00d`
byte for byte; they also match the historical public snapshot linked in the
[API provenance](README.md). The current library has nine mathematical leaves,
ten test modules, two additional aggregate imports and core Lake options; the
historical complete-input binding no longer applies. The measurement is **not**
a new benchmark of the current sources. The Linux worker had a reported 15 GiB
runtime memory limit.
The build and audit recorded `LEAN_NUM_THREADS=1` and `LAKE_JOBS=1` as set;
`LAKE_JOBS` did not provide effective Lake parallelism control, and
`LEAN_NUM_THREADS` is not a global memory cap. The cache-verification process
left those variables unset. CPU model, clock and storage throughput were not
recorded, so this is a workload baseline, not a hardware-normalized rate.

| Workload | Observed result and scope |
| --- | --- |
| `lake --wfail build` | 24.865 seconds wall time, with matching mathlib cache installed and no previous project outputs; all 17 historical library/test modules built. Largest child maximum RSS was 1,328,464 KiB, not aggregate process-tree or machine memory. |
| Matching-cache verification | 5.336 seconds for `lake exe cache get` **after** successful installation/download. This is not the time for a first download. |
| Historical separate stored-proof audit | One nonempty project module per process: 150 raw declarations, 141 stored bodies and nine structural items in total. Maximum sampled cgroup working memory was 8,252,477,440 bytes (about 7.69 GiB), and anonymous memory 4,714,618,880 bytes (about 4.39 GiB); these are shared cgroup measurements, not per-process RSS. Imported dependencies were byte-bound, not proof-rechecked. This historical replay is not required for an ordinary build. |

For planning, expect **tens of seconds to a few minutes** for this project's
default build once the matching dependency cache is ready on a comparable worker;
this range is an estimate, not another measurement or a guaranteed upper bound.
Initial downloads/decompression require additional network time and disk space;
their cold-install cost was not measured by the cache-verification receipt.
Keep the default library and test targets enabled. Follow the README's cache-first
commands; do not silently replace a failed cache fetch with a mathlib source build.

The historical separate audit used a 15 GiB environment with per-process safety
stops at 11 GiB cgroup working memory, 10 GiB anonymous memory or 720 seconds.
These historical limits are not a proven minimum or sufficient bound for another
machine or larger library. Working memory means
`max(0, memory.current - inactive_file)`, sampled every 0.25 seconds. Some runs
recorded `memory.events:max` increments (up to 718); measured OOM/kill increments
were zero. The baseline therefore does not establish an unconstrained memory
peak or absence of limit pressure. Required complete transitive standard-axiom
checking remains distinct from the 38 current selected public `#print axioms`
checks (39 in the historical snapshot) and this stored-proof measurement.

This is proof-oriented infrastructure; it promises no efficient executable
algorithm or runtime complexity. Build/check cost depends on the pinned compiler,
dependency cache, machine and selected audit. These existing measurements provide
standalone planning guidance, not a portable performance guarantee. The library
does not yet supply a general coherent-sheaf theory or claim complete coverage
of any mathematical source. See the root README for the library's current scope.
