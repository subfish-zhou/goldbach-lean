# Release notes: toward v1.0.0

Compared with **v1.0.0-rc1**, commit
`976e60343f5cc50b2f5b2b980de21124e5afc662`.

This revision preserves the public Chen 1+2 theorem and its eventual `0.67`
representation lower bound. It improves proof reuse, local proof structure,
and project navigation. It does not prove binary Goldbach, provide an explicit
threshold, or establish the separate 1+1.9 result.

## Lean source size

Count nonblank physical lines after removing Lean line comments and nested
block comments, including documentation comments. Retain string literals and
code preceding an inline comment. Include root Lean entry files and all Lean
files in the four project source directories, including newly added helpers.
Exclude dependencies, build output, Markdown, tooling, and external optimization
artifacts. These are source lines, not theorem counts or proof-term sizes.

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
The total above includes it; fewer lines need not mean fewer modules.
Counts compare the complete source trees, not a sum of overlapping
optimization batches. A scanner that also erases strings will undercount both
trees by 33 lines and is not the counting convention used here.

Reproduce the current count with `python3 scripts/check.py --static-only --count-lines`.
The same `count_code_lines` function applied to the Git blobs of `v1.0.0-rc1`
reproduces 233,282. Markdown, Python, and TeX are not included in either total.

## Proof-path improvements

### Shared estimates instead of parallel implementations

The dependency audit examined 166 groups of structurally identical theorem
types. Of these, 95 required reuse changes, 39 already reused an existing proof,
and 32 were trivial wrappers. Identical types alone were not treated as a reason
to merge declarations: import direction, existing providers, and public APIs
were checked before changing consumers.

Shared logarithmic and scalar estimates now live below their consumers in
[LogPowerBounds](../MathlibNt/Analysis/LogPowerBounds.lean),
[large-sieve LogPowerBounds](../MathlibNt/AnalyticNumberTheory/LargeSieve/LogPowerBounds.lean),
[PanQuotientBounds](../MathlibNt/AnalyticNumberTheory/LargeSieve/PanQuotientBounds.lean),
[SuzukiEndpointScalarBounds](../MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiEndpointScalarBounds.lean),
and [SuzukiFixedGapRpowMargin](../MathlibNt/SieveTheory/LinearSieve/Suzuki/SuzukiFixedGapRpowMargin.lean).
Consumers apply these providers instead of maintaining independent versions
of the same estimate. Public forwarding lemmas remain where they preserve the
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
and fixed-gap power estimates use the shared scalar layer. This replaces
parallel cutoff and moving-head implementations with a common dependency path,
without introducing a reverse import.

### Character counts use the common bound

In [VaughanDirectAPNormalizedTypeIIActualPhysical](../MathlibNt/AnalyticNumberTheory/Vaughan/VaughanDirectAPNormalizedTypeIIActualPhysical.lean),
`card_primitiveCharacter_le_totient` now directly applies
`primitiveCharacter_card_le_totient_basic`. The public alias is retained, but
the finite-cardinality argument is no longer repeated in that consumer.

### Explicit order and algebra steps

The cutoff square-root comparison now uses `le_of_sq_le_sq`, with the power
identity proved explicitly, rather than asking nonlinear arithmetic to search
the entire local context. Its logarithmic estimates use `add_le_add` to expose
the exact inequalities being combined.

A subsequent ten-shard pass replaced 44 local automation points across 20 files
in Suzuki, Chen1973, large-sieve, Vaughan, Dirichlet L-function, arithmetic,
switching, and PNT modules. Examples include multiplication and division
monotonicity, cancellation with an explicit nonzero premise, square comparison,
and positivity-to-strict-order conversions. Additional moving-head product and
quotient steps use the same approach. Automation remains where it makes the
proof clearer; tactic occurrence counts are not performance measurements.

### Public mathematics stays fixed

The literal specification in [Goldbach/Statement.lean](../Goldbach/Statement.lean)
and the public endpoints in [Goldbach/Theorem.lean](../Goldbach/Theorem.lean)
are unchanged from the release candidate. The qualitative and quantitative
endpoints share the proved Liu-Pan distribution input but remain distinct
declarations. The qualitative public theorem does not directly call the public
quantitative theorem. No public conclusion was weakened and no mathematical
premise was added to a public endpoint. No custom axioms, proof placeholders, or
kernel bypasses were introduced.

## Navigation and dependency views

The README now provides a mathematical roadmap. The
[architecture guide](ARCHITECTURE.md) adds a source-backed import graph,
a shared-declaration example, and grouped source links. The old separate module
guide was merged into that page, removing redundant navigation and historical
file-splitting notes while retaining mathematical explanations and attribution.

LeanArchitect extracts declaration metadata and dependencies; LeanBlueprint
renders mathematical documents and dependency graphs from blueprint data.
They are complementary tools, not alternative proof checkers. The curated
diagrams distinguish mathematical implication, direct imports, and declaration
references; historical optimization exports are not presented as fresh release
graphs.

An executable [Blueprint](../Goldbach/Blueprint.lean) now supplies seven selected
nodes and six automatically inferred endpoint edges. Three input nodes explicitly
exclude upstream display dependencies to define the diagram boundary; their Lean
proof dependencies remain intact. The renderer links declarations to the source
positions exported by LeanArchitect, pinned to the Git revision used to render.
CI builds a downloadable `goldbach-blueprint` website artifact after the proof
checks. It is also included under `blueprint/` in the complete API website.
See the [build instructions](ARCHITECTURE.md#interactive-blueprint).
The seven-node Blueprint is a curated explanation, not an exhaustive project graph.

The API website uses the same doc-gen4 renderer as mathlib documentation and
covers all four project libraries, with declaration search, source links pinned
to the checked-out revision, and links to external dependency documentation.
Mathlib's external documentation is a rolling website, not a version-pinned
proof dependency. Successful main-branch verification is required before
GitHub Pages deployment. See [DOCUMENTATION.md](DOCUMENTATION.md).

## Verification and performance

The release gates are a full warning-fatal build, literal public statement and
standard-axiom checks, script regression tests, an independent replay of
`Goldbach.Theorem`, and validation of the complete documentation website.
The replay checks that module over its cached imports, not a fresh independent
replay of the entire import closure. Blueprint checks distinguish the seven
selected nodes and six endpoint edges from the full proof dependency graph.
See [VERIFICATION.md](VERIFICATION.md) for the separate acceptance gates and
isolated reconstruction instructions.

Warnings are treated as build failures rather than globally suppressed.
Cleanup covers unused variables, redundant tactics and simplifier arguments,
deprecated names, and explicitly scoped unused section instances. Where an
unused binder received an underscore prefix, in-tree named-argument consumers
were updated as well. The public theorem statements remain unchanged.

[BUILD_BENCHMARK.md](BUILD_BENCHMARK.md) defines the clean-project timing
boundary and records the historical 36-minute-23-second baseline. The new
measurement uses a separate checkout with cached pinned dependencies and no
compiled project modules. Incremental builds and concurrent shard timings
are not used as substitutes. Source-size reduction and build time are separate
measurements; single-run timings do not establish a hardware-independent speedup.