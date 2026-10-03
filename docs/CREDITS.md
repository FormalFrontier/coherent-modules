# Contributors and provenance

Authors: Formal Frontier Agents. Original project contributions are provided
under the [Apache-2.0 license](../LICENSE). These are contributions by AI
agents; collective author credit does not identify a legal copyright owner.
No human peer review, source-author endorsement or mathematical novelty is
implied. Review applies to the exact version reviewed, not later changes.

## Mathematical work

Anchor contributed the original coherent-module foundation, kernel closure and
universal-coherence construction, coordinated integration, and wrote the
standalone guide. Other Formal Frontier AI-agent contributors developed the
finite-free kernel characterization, quotient and cokernel closure, coherent
module category, localization and descent, finite-presentation bridge and
exact-five criterion, extension closure, and Hom and tensor closure. The
finite square-zero kernel equivalence, whole-extension finiteness, projection
base change and finite-type ideal/module transfer, together with their zero and
torsion examples, are original Formal Frontier AI-agent contributions. The
tracked examples, aggregate imports and adaptations are collective project work.
The concise contributor lines in the Lean files credit that work
without treating pooled execution identifiers as human names. Original
revision-specific authorship and review records are maintained separately;
this document does not transfer credit to the integrator.

## Tooling and background

Anchor adapted this project's [API adapter](../scripts/generate_api.py) from
earlier Formal Frontier work in algebraic-direct-limits, itself adapted from
ideal-completion, under the same original-project Apache-2.0 authorization.
The preserved historical adapter inventory covers seven mathematical leaves,
an aggregate and nine test modules; it binds 54 native library display sites to
source ranges and distinguishes 39 source docstrings from 15 authored API notes. The
[reference](API.md) contains those historical native signatures, docstrings and
notes rather than vendored documentation-site assets. The current
[square-zero](../CoherentModules/Algebra/TrivSqZeroExt/Finite.lean) and
[ideal/module transfer](../CoherentModules/RingTheory/Ideal/FiniteModuleTransfer.lean)
modules supply their own source documentation.

Lean, mathlib and doc-gen4 are independent tools or dependencies; their
authors and notices remain with their upstream projects and no dependency
website or source tree is distributed here. Mathematical background includes
Kazuhiro Fujiwara and Fumiharu Kato,
[*Foundations of Rigid Geometry I*](https://arxiv.org/abs/1308.4734v5),
and classical coherent-ring theory. No PDF, scan, substantial excerpt or
mathematical-source endorsement is bundled or claimed. Background citation
is not a complete formalization or rights clearance; release review separately
examines attribution, proof integrity and any concrete redistribution concerns.
