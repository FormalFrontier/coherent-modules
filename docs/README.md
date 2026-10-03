# API reference generation

[API.md](API.md) is a frozen historical reference for 54 native display sites in
seven mathematical leaves: classes, constructors, class fields, instances,
definitions and theorems. Its original aggregate and nine test/audit modules
belong to a historical 17-module inventory, not the current nine-leaf,
ten-test-module library. The current
[`TrivSqZeroExt` finite-kernel and base-change API](../CoherentModules/Algebra/TrivSqZeroExt/Finite.lean)
and [`Ideal` finite-module transfer API](../CoherentModules/RingTheory/Ideal/FiniteModuleTransfer.lean)
are documented in their source files and the [mathematical guide](Guide.md),
not in the frozen reference. Test modules are not re-exported by `CoherentModules`.

Read the [mathematical guide](Guide.md) for hypotheses and usage and
[CREDITS.md](CREDITS.md) for provenance. Native display sites are not a complete
kernel-declaration inventory: private examples, helpers and generated declarations
also require complete transitive standard-axiom checking for acceptance.

## Preserved information

For the historical inventory, the bounded adapter preserves native visible
header tokens, including implicit arguments and literal modifiers, normalizing
whitespace only. It verifies each
module/name/kind, signature hash, docstring hash and source range against the fixed
inventory. Native pretty-printing depends on source namespaces, notation and type
inference; displayed fragments are not promised to elaborate in isolation.

There are 39 native source docstrings and 15 separately authored explanations,
labeled **API note (not a source docstring)**. The latter live in
`scripts/api_notes.json` and require semantic review; they are not fabricated
source documentation. Constructors and class-field projections may point to the
whole class declaration. Twelve additional nonprivate raw names, such as generated
recursors, have no native display site; the separate proof inventory accounts for
them rather than inventing documentation signatures.

This library ships Markdown, source links and JSON provenance, not the native HTML
website, JavaScript, styles, fonts, search or dependency documentation. No external
documentation host is required to read its own API. Historical native source URLs
use the original analyzed development revision and are checked as exact strings,
not claimed to be live public web links. The [historical release snapshot](https://github.com/FormalFrontier/coherent-modules/tree/15f0ec72ac0fc053e4243d856c56add4e06b29ce)
provides source navigation for all original inputs when that repository is
accessible; the API's relative source links point into this checkout for the
original seven leaves. The earlier header edits preserved their source line
counts but changed their *source-byte hashes*. Additional current source and
configuration changes also differ from the historical snapshot. This is not
evidence of native generation on the current library.

## Historical native reproduction

The [frozen manifest](api-manifest.json) records native generation against
development revision `91e1a1e8881ef55c045b3a5eb5285875be21a00d`. Its 20
source/pin hashes, three tooling-input hashes and generated-API digest also
matched the complete independent public-release snapshot at
`15f0ec72ac0fc053e4243d856c56add4e06b29ce`. To reproduce this **historical**
binding, check out exactly that public-release commit in a *separate* clone,
not the current library:

```sh
git clone https://github.com/FormalFrontier/coherent-modules.git coherent-api-snapshot
cd coherent-api-snapshot
git checkout --detach 15f0ec72ac0fc053e4243d856c56add4e06b29ce
```

This GitHub history is independent of the analyzed development revision; if the
original object is absent, the adapter requires exact equality of all 20
manifest source/pin hashes rather than pretending native generation took place
at the public-release commit. The native URLs still name the original revision.
Do not run this recipe on the current library and claim it reproduced the frozen
manifest: the earlier eight header edits changed eight source-file hashes, and
the current aggregate imports, added modules and Lake options change more inputs.
The original seven leaves still provide the linked historical source ranges.

Use a separate unchanged doc-gen4 checkout at
`97d4ecdfc8e09e7f511724c25e303d448de6a3db`, including its committed manifest,
with Lean `v4.34.0-rc2`. Build that core-only tool with `lake build doc-gen4`.
Do not add it to this library or change the mathematical dependency pins.
In the library checkout, first successfully fetch the matching mathlib cache and
build all default targets as described in the root README. The following Bash
commands require Python3 and all 17 historical built modules:

```sh
docgen_executable=/absolute/path/to/doc-gen4
docs_work=$(mktemp -d)
mkdir "$docs_work/analysis" "$docs_work/rendered"
source_revision=$(python3 -c 'import json; print(json.load(open("docs/api-manifest.json"))["analyzed_source_revision"])')
for leaf in Basic FinitePresentation Hom Localization ModuleCat TensorProduct UniversallyCoherent; do
  lake env "$docgen_executable" single --build "$docs_work/analysis" "CoherentModules.$leaf" api.db "https://github.com/FormalFrontier/coherent-modules/blob/$source_revision/CoherentModules/$leaf.lean"
done
lake env "$docgen_executable" single --build "$docs_work/analysis" CoherentModules api.db "https://github.com/FormalFrontier/coherent-modules/blob/$source_revision/CoherentModules.lean"
for leaf in Axioms Basic FinitePresentation FinitePresentationZero Hom Localization ModuleCat TensorProduct UniversallyCoherent; do
  lake env "$docgen_executable" single --build "$docs_work/analysis" "CoherentModulesTest.$leaf" api.db "https://github.com/FormalFrontier/coherent-modules/blob/$source_revision/CoherentModulesTest/$leaf.lean"
done
lake env "$docgen_executable" bibPrepass --build "$docs_work/rendered" --none
lake env "$docgen_executable" fromDb --build "$docs_work/rendered" --manifest "$docs_work/rendered/manifest.json" "$docs_work/analysis/api.db"
python3 -B scripts/generate_api.py --native-data "$docs_work/rendered/doc-data" --source-revision "$source_revision" --check
python3 -B scripts/test_generate_api.py --native-data "$docs_work/rendered/doc-data"
```

Create both directories before invoking the native SQLite opener. Run the tool in
this project's `lake env` so imports resolve to its pinned compiled modules.
Retain actual argv, output, exit status, resolved artifacts and both manifests;
native warnings or failures must not be hidden. `single` receives a URL without
fragment; the native linker adds `#Lstart-Lend`. The adapter requires the exact
repository, full revision, module-specific path and recorded bounded range.

## Independent public history and data checks

`api-manifest.json` binds the original 17 source files and three configuration/pin files,
module paths, tool/source revisions, three adapter/inventory/note hashes, canonical
native-record hashes, exact display names and the generated API hash. Checkouts
with unchanged inputs can reuse native evidence through exact equality of
all 20 historical inputs; the current library has different source and Lake
configuration inputs and **does not** meet that byte-equality condition. The
frozen reference and manifest are not a current native-generation or complete-API
claim. A new complete API reference would require its own reviewed inventory and
native checks; the historical generated files remain unchanged.

When the historical source commit exists, the adapter compares every input against
that Git object. A parentless public release need not contain development history.
Only Git's explicit missing-object result, or a source-only tree without a `.git`
marker, enables fallback to the committed manifest's exact hashes. Broken Git
repositories, command failures and wrong object types refuse fallback. `--check`
compares both complete generated files byte for byte. After a reviewed inventory
update, omit `--check` to generate new files from matching native records.

The data tests require the supplied native-record directory and exercise positive
reproduction, malformed records, source/pin drift and source-only/parentless Git
contexts. They do not rerun doc-gen4 or Lean and do not authenticate the provenance
of arbitrary supplied JSON. Real native receipts require independent inspection.
Neither adapter hashes nor successful rendering certify proofs, rights or release
acceptance. Full review remains separate.
