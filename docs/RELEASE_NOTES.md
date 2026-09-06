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
| MathlibNt | 201,703 | 192,389 | -9,314 |
| AnalyticNumberTheory | 16,003 | 13,868 | -2,135 |
| PrimeNumberTheoremAnd | 15,477 | 15,076 | -401 |
| Root entry files | 44 | 44 | 0 |
| **Total** | **233,282** | **221,487** | **-11,795 (-5.06%)** |

The Lean source file count changes from **729 to 735**. Five focused helper
modules replace repeated local arguments, and one isolated module annotates
existing declarations for Blueprint. Without its 55 lines of presentation
metadata, the proof source is 221,432 lines, a reduction of 11,850 lines (5.08%).
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
quantitative theorem. No theorem assumptions were weakened to obtain the line
reduction, and no custom axioms, proof placeholders, or kernel bypasses were
introduced.

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
checks. See the [build instructions](ARCHITECTURE.md#interactive-blueprint).
This is not an exhaustive project graph or an automatically published Pages site.

## Verification and performance

After the 20-target integration check, the final source tree passed the full
build (735 source modules), literal public statement and standard-axiom checks,
14 checker tests, and an independent replay of `Goldbach.Theorem`. The replay
checks that module over its cached imports, not a fresh independent replay of
the entire import closure. The Blueprint was rendered and checked for seven
nodes, six edges, resolved labels, and source links; desktop and mobile browser
checks confirmed graph display and node selection. CI repeats the build and
verification on the pushed revision. See [VERIFICATION.md](VERIFICATION.md)
for the separate acceptance gates and isolated reconstruction instructions.

**No cross-version build-time comparison is reported.** The original version
and the current revision were built on different machines. Historical local
experiments and concurrent shard timings are not used to claim an overall
speedup. The source-size reduction above is independent of build hardware.