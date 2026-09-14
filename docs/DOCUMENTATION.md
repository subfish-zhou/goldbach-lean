# Project website, Lean documentation and dependency views

The complete static-site layout has five routes, relative to the project's
deployment prefix:

- **Project homepage** at `/`: research goals, progress, reading routes,
  verification instructions and provenance links. Chen's **1 + 2 theorem** is
  formalized alongside **Li–Liu's 1+1.9 theorem**, with stronger results as
  further research directions. The homepage HTML and CSS live in `website/`.
- **Lean API documentation** at `/docs/`: doc-gen4 module pages, declaration
  search, declaration anchors, source links, imports and reverse-import links
  for the documented modules.
- **Proof Blueprint** at `/blueprint/`: the selected **Chen 1+2** and
  **Li–Liu 1+1.9** routes together with their reusable analytic foundations,
  with links into the implementation.
- **Author report** at `/report/`: the Li–Liu result, its two proof exits,
  paper-to-Lean correspondence and review scope, authored in `website/report/`.
- **Full structure explorer** at `/structure/`: the four-library module
  inventory and compiled declaration references, with separate public-exit role labels, generated separately from
  existing Lean objects and assembled with the other views.

This documentation update uses an independent local static-site build followed
by publication to `gh-pages`. The commands below describe that release path;
the deployed version is established by reading the live build records after
Pages finishes, not by the presence of these instructions in the source tree.

The completed public theorems give Chen's prime-plus-almost-prime representation
and Li–Liu's constrained `N = p + r*q` representation with `r^10 ≤ q^9`, together
with quantitative bounds for their respective distinct-prime counts.
[THEOREMS.md](THEOREMS.md) defines their precise mathematical scope.
The proofs use Lean's standard logical foundation: `propext`, `Classical.choice`
and `Quot.sound`. [VERIFICATION.md](VERIFICATION.md) describes the source build,
literal statement checks, axiom reports and kernel replay. The documentation
pipeline below renders compiled declarations and checks the resulting site.

The current source entries are `Goldbach` for 1+2, `Goldbach.OnePlusOneNine`
for 1+1.9, and `Goldbach.All` for both. Blueprint annotations in
`Goldbach/Blueprint.lean` select substantive mathematical stages from both routes
and their analytic foundations. `blueprint/nodes.json` records their mathematical
titles, source declarations and roles. After editing that curated catalogue,
run `python3 scripts/generate_blueprint.py` to regenerate the annotations;
`--check` verifies synchronization without writing. This is mechanical code
generation, not automatic mathematical node selection. The master `blueprint/src/content.tex`
includes the overview and proof chapters in `blueprint/src/chapters/`.
LeanArchitect infers dependencies from compiled declarations; LeanBlueprint
renders the exposition and both global and chapter-sized graphs. After a reviewed
catalogue change and a successful render, `python3 scripts/update_blueprint_graph.py`
checks the new graph against the approved exits; add `--write` to refresh
`blueprint/graph.json`. Changing the exit contract requires explicitly repeating
`--terminal LABEL` for each approved exit. The command reads actual rendered DOT
and requires every selected node to reach an approved exit. Continue with
`python3 scripts/verify_blueprint.py` to check the updated snapshot and source links.
Run these commands in the activated Blueprint environment so its `plastex` and
`pygraphviz` dependencies are available. Chapter graphs
include immediate external inputs, marked `(input)`, without inventing edges.
`scripts/verify_blueprint.py` checks the exact graph inventories, chapter-edge
reachability, paths from every selected node to a documented theorem exit,
mathematical display titles, and source-file targets. These are structural
regression checks; mathematical coverage and teaching clarity require separate
review. The [coverage guide](../blueprint/COVERAGE.md) records where the principal
counting, sieve, distribution, integral and error-budget obligations are explained.
The `\sourcefile{path}{title}` macro pins background reading links to the
Blueprint's own source revision at rendering time.

Stable entry pages are `overview.html`, `foundations.html`, `chen.html` and
`liliu.html` beneath `/blueprint/`. They are resolved from rendered chapter IDs,
so adding a chapter cannot silently redirect a homepage link to the wrong topic.

The generated API inventory retains its own `source_revision` in
`docs/build-info.json`. The assembled site's record distinguishes
`api_source_revision`, `website_source_revision`, `blueprint_source_revision`
and `structure_source_revision`;
`structure/build-info.json` records the structure export's source revision and
input fingerprint. The API source version and website version may differ when
reusing a verified complete API artifact. Record both exact commits, preserve
the API's original source links, and check compatibility with the current
module inventory and linked declarations. Pass `--source-revision COMMIT` to
`scripts/build_site.py` to identify the website source; the Blueprint record
must match it. An older API must never be relabelled as newly rendered output.
Keep the report's own source pins and review scope alongside these identities.

## Pinned generator and isolation

The nested `docbuild/` Lake project uses Lean `v4.33.0-rc1` and doc-gen4's
[official matching tag](https://github.com/leanprover/doc-gen4/tree/v4.33.0-rc1),
frozen at `498457dedc5bf2eb884c5100804ef24c96b92a08`. Its committed manifest pins
all generator dependencies. The theorem project and its core `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain` remain independent of this generator
project. Documentation dependencies live under `docbuild/.lake/packages`;
the generator reads the theorem project's existing mathlib installation in place.

The [upstream README](https://github.com/leanprover/doc-gen4/blob/v4.33.0-rc1/README.md)
recommends a nested Lake project. Its normal `:docs` facets recursively document
imports and Lean core. At this pinned version those facets and the renderer
provide no external-documentation base-URL option. `GoldbachDocs.lean` therefore
calls the unmodified upstream analyzer, HTML renderer and search-index writer
for **project modules only**. It retains the complete imported name-to-module
context for declaration links. A Python postprocessor redirects dependency links
in HTML and search/header JSON.

Dependency API links use <https://leanprover-community.github.io/mathlib4_docs/>.
This moving documentation reference can contain declarations or anchors that
differ from the project's pinned mathlib. Use `--mathlib-docs URL` to select a
compatible hosted snapshot when available. LeanArchitect imports link to their
pinned GitHub source. Source links for project declarations use the checkout's
Git commit and line ranges. Generate from a clean, committed release checkout,
and publish that commit to make its source links publicly resolvable.

## Independent Lean CI and local documentation

`.github/workflows/lean.yml` verifies source pushes other than `gh-pages`, pull
requests and manual runs. It retains the full warning-free library build,
source/statement/axiom checks, script tests and public-module kernel replay:

```sh
lake --wfail build
python3 scripts/check.py
python3 -m unittest discover -s scripts -p 'test_*.py'
lake env leanchecker --verbose Goldbach.Theorem
lake env leanchecker --verbose Goldbach.Checks
lake env leanchecker --verbose Goldbach.OnePlusOneNine
lake env leanchecker --verbose Goldbach.OnePlusOneNineChecks
lake env leanchecker --verbose Goldbach.All
```

These gates remain independent of documentation generation. The Lean workflow
has no website generation or deployment job; pushing generated files to
`gh-pages` does not restart the proof workflow. It keeps a 180-minute job budget,
a 160-minute build-step budget and the build timing/runner-context artifact.
Those limits are safety budgets, not measured speed improvements.

The project build cache is keyed by platform, toolchain, dependency manifest,
Lake configuration and revision, with a same-configuration incremental fallback.
Lake and the checks run even on an exact cache hit. Local documentation reads
stable, previously verified compiled inputs; its generator has a separate
dependency installation. Reusing those inputs requires matching source and
configuration evidence. Static validation and publishing do not replace the
Lean build, checks or replay. Compare cold-cache and warm-cache timings
separately, and keep local measurements distinct from GitHub runner results.

## Build a complete API site

Requirements: the pinned Lean/Lake toolchain, a C compiler, Git, Python 3.11 or
newer, network access for the generator's first build, and sufficient disk space
for its native executable and the project API pages. Finish the project build
before starting documentation generation, so all compiled proofs and runtime
sidecars are ready and remain stable throughout rendering:

```sh
lake --wfail build
python3 scripts/build_docs.py
```

The default API output is `docbuild/.lake/build/api/`. Choose a fresh path with
`--output` for each later run. Each invocation generates into a fresh intermediate
directory and publishes the output after validation. Failed runs leave diagnostic
intermediates under `docbuild/.lake/build/api-run-*`. These directories are
ignored build products.

With its default module selection, the script enumerates **every source module**
in all four libraries, including modules outside facade import closures:

- `Goldbach`
- `MathlibNt`
- `AnalyticNumberTheory`
- `PrimeNumberTheoremAnd`

It builds the generator, reads the project's compiled `.olean` artifacts and
runtime sidecars, renders the selected modules, waits for every renderer, then
writes the upstream declaration and header search indexes. The main options are:

| Option | Effect |
|---|---|
| `--module NAME` | Select a module; repeat the option to select several. The default selects all four libraries. |
| `--jobs N` | Run at most `N` module renderers concurrently; the default is `2`, and `1` serializes rendering. |
| `--output PATH` | Publish to a new directory after validation. |
| `--artifacts-from PATH` | Read project artifacts and dependencies from a matching compiled checkout. |
| `--mathlib-docs URL` | Set the external dependency API base URL. |
| `--blueprint PATH` | Include an already rendered Blueprint inside a legacy API bundle. |

Choose renderer concurrency to fit available memory and CPU resources. The driver
also defaults `LEAN_NUM_THREADS` to `2` when the environment leaves it unset.
Generated module HTML covers the selected project modules; mathlib, Lean core
and generator-library references link outward. Project tactic declarations appear
on their module pages; the global upstream tactic catalogue remains empty.

Validation checks module coverage, declaration search anchors and local HTML
asset/link targets. Omitted declaration analysis reported by doc-gen4 fails the
run. `build-info.json` records the source revision, toolchain, generator and
mathlib revisions, renderer concurrency, module inventory, declaration count,
external URL count and full/partial scope. Release website assembly requires a
full API build.

## Small-module smoke test and artifact reuse

```sh
lake --wfail build Goldbach.Statement
python3 scripts/build_docs.py --module Goldbach.Statement \
  --output docbuild/.lake/build/smoke-site
python3 -m http.server 8000 --directory docbuild/.lake/build/smoke-site
```

Visit <http://localhost:8000/Goldbach/Statement.html>, search for
`Goldbach.ChenTheorem`, follow its declaration anchor and source link, and inspect
the external `Nat.Prime` and import links. Serve over HTTP so the fetch-based
search interface can load its indexes.

To reuse prebuilt artifacts, add `--artifacts-from /path/to/compiled-checkout`.
First finish and verify the corresponding project build on the same proof
branch, including transitive dependencies. The script reads that checkout in
place and runs Lake only in the documentation generator project. Its preflight
compares the toolchain, core dependency manifest and selected source hashes,
and checks that the selected `.olean` files exist. The completed project build
supplies the freshness guarantee for transitive artifacts.

## Assemble the project website

Build the Blueprint using the [normal procedure](ARCHITECTURE.md#interactive-blueprint),
including `python3 scripts/verify_blueprint.py`, which writes its build record.
Generate the structure export from the same stable compiled project, then supply
its pre-generated `structure/` directory to the assembler. In this example,
`api-release`, `structure-release` and `site-release` must all be new paths;
`SITE_REVISION` is the exact committed website/Blueprint source revision:

```sh
SITE_REVISION=$(git rev-parse HEAD)
python3 scripts/build_docs.py --output docbuild/.lake/build/api-release
python3 scripts/build_project_structure.py \
  --api docbuild/.lake/build/api-release \
  --source-revision "$SITE_REVISION" \
  --output docbuild/.lake/build/structure-release
python3 scripts/build_site.py --api docbuild/.lake/build/api-release \
  --blueprint blueprint/web \
  --structure docbuild/.lake/build/structure-release/structure \
  --source-revision "$SITE_REVISION" \
  --output docbuild/.lake/build/site-release
python3 -m http.server 8000 --directory docbuild/.lake/build/site-release
```

If a compatible full API output already exists and has been verified, skip API
generation and use that path in both later commands. Likewise, a structure
export can be reused with matching source/object fingerprints and valid API
links. `build_project_structure.py --output DIR` writes `DIR/structure/`;
`build_site.py --structure` takes that inner directory, not `DIR` or the
unpopulated `website/structure/` template directory. The assembler requires
`--structure` and checks that its module inventory matches the full API inventory.

The resulting routes are `/`, `/docs/`, `/blueprint/`, `/report/` and
`/structure/`. `build_site.py` combines the full API output, rendered Blueprint,
pre-generated structure export, homepage assets and authored `website/report/`
pages in a fresh output tree. It checks declaration coverage and local links
and anchors within the complete deployment boundary. Assembly reads static
inputs and leaves their trees unchanged; it performs neither Lean compilation
nor API rendering nor structure extraction. Preserve every route together when
previewing or publishing, because navigation and data links cross subdirectories.

Both API-only output and the older `build_docs.py --blueprint` bundle are valid
assembly inputs. For a legacy bundle, the copy step omits its nested Blueprint
and places the separately supplied Blueprint at the sibling `/blueprint/`
route. A partial API build fails the assembly preflight.

Without `--source-revision`, the website source revision defaults to the API
revision. Supply it explicitly when the website/Blueprint comes from a newer
commit. Preserve the separate API, website, Blueprint and structure identities
and inspect the report's fixed source links; a homepage hash or a matching
module count alone cannot establish provenance for all these inputs.

### Three graph meanings

The structure exporter reads all four libraries, including modules outside the
public facades' import closures. Its declaration census uses actual
`ModuleData.constNames`, cross-checked against stored constants, and retains
every provider of repeated names. The reading views have different edge meanings:

| View | Edge meaning and direction |
|---|---|
| Curated mathematical Blueprint | Selected explanatory prerequisite → consumer; LeanArchitect supplies dependencies for the authored selection. |
| Module import graph | Consumer module → direct source import, cross-checked against compiled imports. This records module access, not use of a particular proof. |
| Compiled declaration reference graph | Declaration → `Expr.const` reference in its `type`, proof/definition `value`, or `recursorRHS`, kept as separate edge types. |

Only the compiled value-reference layer records actual static references in a
stored proof or definition value. An import path is never a proof/value path.
The compiled graph retains cycles and self-references, generated declarations,
and exact names at the external or unresolved boundary; it is not forced into
a DAG. References outside the local census are not recursively expanded.
These are static expression references, not tactic execution traces or dynamic
runtime calls. The exporter fingerprints source and object bytes and checks
import agreement; proof verification remains the responsibility of Lean's
build/check/replay gates. See [the architecture guide](ARCHITECTURE.md#reading-dependency-data).

The Blueprint's plasTeX configuration selects the `HTML5` renderer, loads
`plastexdepgraph` and `leanblueprint`, copies theme extras, and loads local
packages and templates. It sets `split-level=0`, `localtoc-level=0` and
`mathjax-dollars=False`. LeanArchitect's declaration-only setup macros have
explicit empty HTML templates, so they emit no visible body content while
parser warnings remain enabled.

Link repair maps two historical relative module URLs to their actual
`AnalyticNumberTheory` pages. Links to compiler-generated proof auxiliaries,
auxiliary definitions and constructor indices omitted by doc-gen4 point to the
owning declaration when that owner's anchor exists on the same page. Validation
rejects other missing anchors. Directory routes must contain `index.html`, and
local links must remain within the deployment boundary. The explicitly
registered declaration-search `find/` route handles its fragments in JavaScript;
other HTML fragments are checked against page anchors, with `#top` accepted as
the page-top destination.

`external_url_count` counts distinct external URLs in HTML attributes and API
index/header metadata. Before release, check external link availability and
Blueprint graph interaction in a browser, alongside the local structural checks.

## Regression tests and deployment

Run the source-only regression suites with:

```sh
python3 -m unittest discover -s scripts -p test_build_docs.py -v
python3 -m unittest discover -s scripts -p test_build_site.py -v
python3 -m unittest discover -s scripts -p test_project_structure.py -v
python3 -m unittest discover -s scripts -p test_publish_site.py -v
python3 -m unittest discover -s scripts -p test_ci_workflow.py -v
```

The site suite exercises API-only and legacy-bundle inputs, preservation of input
trees, cross-navigation and repeated navigation insertion, homepage hashes,
partial-build rejection, revision validation, missing targets, declaration-census
mismatches, directory routes and deployment-boundary escapes. It also checks that
Blueprint navigation is added to the page header while theorem headers remain
intact.

For Pages, publish the **entire generated site directory**, preserving
`docs/declarations/*.bmp` (JSON indexes despite their extension), `docs/find/`,
JavaScript/CSS, homepage assets, `.nojekyll`, `blueprint/`, `report/` and the
complete `structure/` data shards. Relative links support a project Pages prefix.
Keep Apache-2.0 licensing, upstream copyright notices and the attribution in
[PROVENANCE.md](PROVENANCE.md) intact across the public reading surfaces.

First validate the prepared payload without Git writes:

```sh
python3 scripts/publish_site.py --site docbuild/.lake/build/site-release
```

The publisher checks required routes, full API coverage, exact source identities,
declaration anchors, local links and the static-file inventory. It rejects
private/build directories, symlinks, private paths or credentials in text, and
oversized files or payloads. Keep build logs, raw extraction caches and private
verification ledgers outside the publishable tree.

For an authorized release, use a clean committed source checkout whose `HEAD`
matches `website_source_revision`, with publicly resolvable source commits,
Git push access to the configured repository and authenticated `gh` access to
Pages settings. Require the corresponding Lean acceptance evidence separately;
the publisher does not query CI. Then run:

```sh
python3 scripts/publish_site.py --site <new-complete-site-directory> \
  --publish --configure-pages --staging <new-staging-directory>
```

Replace both angle-bracket placeholders with actual paths. The staging directory
must not exist. The publisher creates a separate Git checkout there, preserves
existing `gh-pages` history, pushes the static tree without force, reads back
the remote branch, and configures Pages to serve `gh-pages` at `/`. Its local
receipt stays in the staging checkout's `.git/publication-result.json`, outside
the uploaded site. It neither commits nor rewrites the source branch.

After GitHub Pages finishes deploying, read the public `build-info.json` and the
API, Blueprint and structure build records; match them to the candidate's exact
versions. Check all five entry routes, declaration search and its destination
anchors, and both graph interfaces under the real project prefix. A successful
push or settings update establishes the publishing request; live read-back
establishes which version is online.

## Local proof-compilation measurements

These are local module measurements, not whole-project or GitHub Actions speedups.
Each pair uses identical frozen dependencies, two physical CPU cores, Lean `-j2`,
and `-DautoImplicit=false -DwarningAsError=true`. Two interleaved AB/BA rounds
compile the module afresh into separate output directories; the table reports
mean elapsed time. Dependency preparation and validation are not included.

| Module | Baseline | Optimized | Local elapsed-time reduction |
| --- | ---: | ---: | ---: |
| `MertensTheorem` | 31.00 s | 13.52 s | 56.4% |
| `LiuPanAggregatePsiCharacters` | 16.10 s | 14.34 s | 10.9% |
| `StandardBVChosenSmallSquare` | 14.57 s | 7.30 s | 49.9% |

The changes restrict arithmetic tactics to the inequalities they need, replace
large-context automation with monotonicity, and share exact scalar shell-sum
identities for noncoprime corrections and prime-number-theorem remainders.
Public statements, definition
values, import compatibility, signed sums, weights, and constants are preserved.

Incremental acceptance checks the changed modules, direct consumers, and public
theorem checks against frozen dependencies, including declaration comparison,
axiom inspection, and targeted kernel replay. A full clean CI measurement remains
a separate integration measurement; these local percentages must not be applied
to the entire project.

A subsequent batch uses the same paired protocol, with the preceding accepted
proof optimizations already present in the dependency baseline:

| Module | Baseline | Optimized | Local elapsed-time reduction |
| --- | ---: | ---: | ---: |
| `SelbergUpperBound` | 15.25 s | 12.48 s | 18.2% |
| `LiuPanPrimePowerLargeSieve` | 16.91 s | 10.76 s | 36.4% |
| `LiLiuGoldbachS1SieveProductLower` | 12.89 s | 7.94 s | 38.4% |
| `LiuPanPrimitivePerron` | 17.07 s | 15.57 s | 8.8% |

This batch replaces general congruence search around a dependent character
conversion with the precise scalar congruence, avoids unnecessary expansion of
local aliases, and narrows arithmetic in divisor sums, the S₁ sieve-product
lower bound and the Perron tail estimates. All original compiled declaration
names, types, universes, declaration kinds and definition values are preserved,
including compiler-generated auxiliaries. No new premise or import change is
introduced, and neither warnings nor release verification gates are weakened.
The S₁ constants and cutoffs, weighted character sums and Perron bounds are
unchanged. Validation remains incremental and these measurements do not predict
whole-project wall time.

Strict downstream verification also exposed an existing unbound implicit `N` in
a private `Switching.Weights` lemma. It is now explicitly written in the same
position and with the same implicit binder information as in the old compiled
constant. Full constant comparison confirms no new premise or type change;
this compatibility repair is not counted as a speed improvement.

## Shared derivative proof tools

The polynomial and elementary derivative tools are now ordinary modules of
`MathlibNt.Tactic`, with regression examples included in the library build.
[Derivative automation](DERIVATIVE_AUTOMATION.md) records their scope, explicit
domain obligations, local normalization timings and generated-name compatibility
limits. The API documentation therefore resolves their imports from the project
itself rather than from an external experimental search path. No timing probe or
private audit object is required to build the project.
