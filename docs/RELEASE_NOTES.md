# Release notes

## Li–Liu 1+1.9

The project now formalizes Li–Liu's 1+1.9 theorem alongside the existing Chen
1+2 development. Every sufficiently large even natural number has a
representation `N = p + r*q`, with `p` and `q` prime, `r = 1` or prime, and
`r^10 ≤ q^9`. A second endpoint gives the equivalent real-power formulation.

The quantitative result counts distinct eligible primes `p` and proves

```text
(1/2500) * (liuSingularSeries(N) * N / log(N)^2) < D19(N)
```

for all sufficiently large even `N`. The coefficient `1/2500` is exactly
`0.0004`. For each fixed real `κ < 515093/800000000`, a further endpoint gives
the eventual non-strict lower bound with coefficient `κ`; its threshold is
chosen after `κ`. [THEOREMS.md](THEOREMS.md) defines the count and the exact
Liu singular-series normalization.

### Imports and existing builds

`Goldbach` retains the 1+2 entry and public names. Import
`Goldbach.OnePlusOneNine` for the four new Li–Liu endpoints, or `Goldbach.All`
for both developments. The package configuration, toolchain and dependency
pins stay fixed. Keep `.lake/` when updating an existing build; Lake can reuse
unchanged dependencies and rebuild the new or affected modules. Use
`lake build Goldbach.Theorem`, `lake build Goldbach.OnePlusOneNine`, or
`lake build Goldbach.All` for the selected public target, and `lake build`
for the full project. The [README](../README.md#focused-builds-and-upgrading-an-existing-checkout)
gives the branch-update commands.

The [verification guide](VERIFICATION.md) separates full source checking,
the separate Chen and Li–Liu acceptance probes, and endpoint inspection. The existing 1+2
verification records retain their original theorem and revision scope.

## Historical release: v1.0.0

The remainder of this page records the **1+2** release, including its source
counts, proof-path changes and measured clean builds.

Compared with **v1.0.0-rc1**, commit
`976e60343f5cc50b2f5b2b980de21124e5afc662`.

The first stable release provides Chen's 1+2 theorem and its eventual `0.67`
representation lower bound, with shared proof infrastructure, a warning-free
build, and a project website linking the mathematical outline and Lean sources.

## Lean source size

Count nonblank physical lines after removing Lean line comments and nested
block comments, including documentation comments. Retain string literals and
code preceding an inline comment. Include root Lean entry files and all Lean
files in the four project source directories, including newly added helpers.
Exclude dependencies, build output, Markdown, tooling, and external optimization
artifacts. The resulting metric is the number of Lean source lines.

| Source area | v1.0.0-rc1 | This revision | Change |
|---|---:|---:|---:|
| Goldbach (including Blueprint metadata) | 55 | 110 | +55 |
| MathlibNt | 201,703 | 192,373 | -9,330 |
| AnalyticNumberTheory | 16,003 | 13,841 | -2,162 |
| PrimeNumberTheoremAnd | 15,477 | 15,076 | -401 |
| Root entry files | 44 | 44 | 0 |
| **Total** | **233,282** | **221,444** | **-11,838 (-5.07%)** |

The Lean source file count changes from **729 to 735**. Five focused helper
modules replace repeated local arguments, and one isolated module annotates
existing declarations for Blueprint. Without its 55 lines of presentation
metadata, the proof source is 221,389 lines, a reduction of 11,893 lines (5.10%).
The total above includes this metadata. Counts compare complete source trees
using one scanner; string literals contribute 33 lines in each tree.

Reproduce the v1.0.0 count from that source revision with
`python3 scripts/check.py --static-only --count-lines`.
The same `count_code_lines` function applied to the Git blobs of `v1.0.0-rc1`
reproduces 233,282. Both totals use the same Lean-only counting scope.

## Proof-path improvements

### Shared estimates

The dependency audit examined 166 groups of structurally identical theorem
types. Of these, 95 required reuse changes, 39 already reused an existing proof,
and 32 were trivial wrappers. Reuse decisions checked import direction,
existing providers, and public interfaces before changing consumers.

Shared logarithmic and scalar estimates now live below their consumers in
[LogPowerBounds](../MathlibNt/Analysis/LogPowerBounds.lean),
[large-sieve LogPowerBounds](../MathlibNt/AnalyticNumberTheory/LargeSieve/LogPowerBounds.lean),
[PanQuotientBounds](../MathlibNt/AnalyticNumberTheory/LargeSieve/PanQuotientBounds.lean),
[SuzukiEndpointScalarBounds](../MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiEndpointScalarBounds.lean),
and [SuzukiFixedGapRpowMargin](../MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiFixedGapRpowMargin.lean).
Consumers now share these providers. Public forwarding lemmas remain where they preserve the
existing API.

### One Suzuki fixed-head route

[SuzukiCutoffClaim146iiiSanitized](../MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiCutoffClaim146iiiSanitized.lean)
now imports
[SuzukiMovingSigmaElementaryHead](../MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiMovingSigmaElementaryHead.lean)
for `exists_sourceSigma_fixed_lower_threshold`,
`fixedCompactPerturbationContract`, and
`lemma133WeightedHeadContract_corrected`. The duplicate long proof bodies and
their duplicate private support lemmas were removed. The fixed-head provider
still supplies the same public statements; the cutoff logarithmic-domination
argument remains a separate consumer.

The fixed-perturbation convergence theorem is provided from
[SuzukiClaim146Quantitative](../MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiClaim146Quantitative.lean),
and fixed-gap power estimates use the shared scalar layer. The cutoff and moving-head implementations now use a common acyclic
dependency path.

### Character counts use the common bound

In [VaughanDirectAPNormalizedTypeIIActualPhysical](../MathlibNt/AnalyticNumberTheory/Vaughan/VaughanDirectAPNormalizedTypeIIActualPhysical.lean),
`card_primitiveCharacter_le_totient` now directly applies
`primitiveCharacter_card_le_totient_basic`. The public alias is retained, but
the finite-cardinality argument comes from the common provider.

### Explicit order and algebra steps

The cutoff square-root comparison now uses `le_of_sq_le_sq` with an explicit
power identity. Its logarithmic estimates use `add_le_add` to expose
the exact inequalities being combined.

Further cleanup replaced 44 local automation points across 20 files
in Suzuki, Chen1973, large-sieve, Vaughan, Dirichlet L-function, arithmetic,
switching, and prime-number-theorem modules. Examples include multiplication and division
monotonicity, cancellation with an explicit nonzero premise, square comparison,
and positivity-to-strict-order conversions. Additional moving-head product and
quotient steps use the same approach. Automation remains where it makes the
proof clearer. Build performance is measured by the clean-build benchmark below.

### Public mathematics stays fixed

The literal specification in [Goldbach/Statement.lean](../Goldbach/Statement.lean)
and the public endpoints in [Goldbach/Theorem.lean](../Goldbach/Theorem.lean)
are unchanged from the release candidate. Each public endpoint uses its own implementation declaration, and both share
the proved Liu-Pan distribution input. The implementation discharges the
analytic premises through proved theorems. Public axiom reports contain only
Lean's standard logical axioms: `propext`, `Classical.choice`, and `Quot.sound`.

## Navigation and dependency views

The README now provides a mathematical roadmap. The
[architecture guide](ARCHITECTURE.md) adds a source-backed import graph,
a shared-declaration example, and grouped source links. The old separate module
guide was merged into that page, removing redundant navigation and historical
file-splitting notes while retaining mathematical explanations and attribution.

LeanArchitect extracts declaration metadata and dependencies; LeanBlueprint
renders mathematical documents and dependency graphs from blueprint data.
The diagrams distinguish mathematical implication, direct imports, and
declaration references. Each view identifies its source and edge convention.

An executable [Blueprint](../Goldbach/Blueprint.lean) now supplies seven selected
nodes and six automatically inferred endpoint edges. Three input nodes explicitly
exclude upstream display dependencies to define the diagram boundary; their Lean
proof dependencies remain intact. The renderer links declarations to the source
positions exported by LeanArchitect, pinned to the Git revision used to render.
CI builds a downloadable `goldbach-blueprint` website artifact after the proof
checks. The project website places this selected-declaration view at
`/blueprint/`, alongside Lean Doc at `/docs/` and the independent homepage at `/`.
See the [build instructions](ARCHITECTURE.md#interactive-blueprint).

The Lean API documentation uses the same doc-gen4 renderer as Mathlib documentation and
covers all four project libraries, with declaration search, source links pinned
to the checked-out revision, and links to external dependency documentation.
Mathlib's external documentation tracks upstream updates; the project's proof
dependency is locked in `lake-manifest.json`. Successful main-branch verification is required before
GitHub Pages deployment. See [DOCUMENTATION.md](DOCUMENTATION.md).

## Verification and performance

The release gates are a full warning-fatal build, literal public statement and
standard-axiom checks, script regression tests, an independent replay of
`Goldbach.Theorem`, and validation of the complete documentation website.
The replay checks `Goldbach.Theorem` against its cached imports. Blueprint checks distinguish the seven
selected nodes and six endpoint edges from the full proof dependency graph.
See [VERIFICATION.md](VERIFICATION.md) for the separate acceptance gates and
isolated reconstruction instructions.

Warnings are treated as build failures.
Cleanup covers unused variables, redundant tactics and simplifier arguments,
deprecated names, and explicitly scoped unused section instances. Where an
unused binder received an underscore prefix, in-tree named-argument consumers
were updated as well. The public theorem statements remain unchanged.

The recorded clean builds took **36:23 for v1.0.0-rc1 and 30:06 for v1.0.0**,
a **17.3% reduction in elapsed time**. Sampled peak proportional memory increased
from **5.97 to 6.85 GiB**; sampled peak resident memory was **10.48 and 10.43 GiB**,
respectively. Each version has one recorded run using the same CPU model and
thread settings. Timing depends on machine load and cache state.

The v1.0.0 run starts from a separate checkout with cached pinned dependencies
and zero compiled project modules. It finishes with zero warnings and matching
proof-source fingerprints before and after the build. The
[benchmark guide](BUILD_BENCHMARK.md) describes the timing and memory methods,
including the recorded sampling failures. Full records are available for
[v1.0.0-rc1](benchmarks/v1.0.0-rc1.json) and [v1.0.0](benchmarks/v1.0.0.json).