# Li–Liu: shared finite-prefix and squarefree-divisor proofs

Starting from the [accepted shared-calculus snapshot](LILIU_SHARED_CALCULUS_CLEANUP.md),
four existing source files save 66 main/Li–Liu effective lines and 49 Chen closure
lines. All 10,408 old public names, declaration kinds and statement hashes remain.
One existing private cardinality theorem becomes public. No module, import or
auxiliary Lean proof is added.

## Squarefree divisor sums

The canonical `LinearSieve.Internal.sum_divisors_eq_sum_primeFactors_powerset`
keeps its complete statement and replaces its manual bijection proof with the
three-line Mathlib proof already used by WF SmallRosser. That original WF public
name becomes a direct call to the canonical theorem. The dependency runs from
WF to the canonical finite-sieve module to Mathlib; it never runs back into WF.
Both original public statements have the same kind/type hash, 3852830595.
The function `f : Nat → Real` remains arbitrary, including signed values.
`Squarefree n` is the original hypothesis: it includes the unit case and excludes
zero. No positivity or nonempty-factor hypothesis is introduced.

## Sorted finite prefixes

The canonical `LinearSieve.sorted_prefix_toFinset_eq_filter_ge` uses symmetry and
the shorter direct sorted-list argument formerly in `LiLiuPrereqWF.rounded_prefix_eq_take`.
The WF public name now calls that canonical identity with symmetry. Both complete
statements remain unchanged. The existing private canonical
`sorted_prefix_card_eq_filter_ge` becomes public with its statement and proof
unchanged; WF's existing `rounded_prefix_card` becomes a direct call to it.
Both original canonical admissibility consumers and the WF cardinality consumer
actually reach the promoted proof. Its original kind/type hash is 2787789504.

Sorting still uses the original natural labels, never rounded real values.
The rounding function need not be injective: equal rounded values retain their
original slots and multiplicities. The inclusive prefix length `i+1`, one-based
parity, strict cubic tests and vacuous empty-set index case remain unchanged.
The complete post-change text of each file is reconstructed from its archived
source using only these proof substitutions and the visibility change, then
compared byte for byte. Rounded definitions, product lemmas and admissibility
equivalences are therefore unchanged, as are all four import lists.

## Measurements

| Existing file | Net effective-line change |
|---|---:|
| LinearSieve/FiniteWeights | -27 |
| LiLiuPrereqWFSmallRosser | -2 |
| LinearSieve/RosserChains | -22 |
| LiLiuPrereqWFRoundedAdmissibility | -15 |
| Complete phase | -66 |

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main modules | 1,803 | 1,803 | 0 |
| Main effective lines | 201,822 | 201,756 | -66 |
| Li–Liu closure modules | 1,432 | 1,432 | 0 |
| Li–Liu closure effective lines | 194,267 | 194,201 | -66 |
| Chen closure effective lines | 99,263 | 99,214 | -49 |

All shared proofs and wrappers are counted. Only the two canonical finite-sieve
modules belong to Chen's closure; their 27+22 savings account for its reduction.
Main physical lines change by -66; UTF-8 bytes by
-2,595. Shared imports count independently in each theorem
closure. External Lake dependencies are excluded. No proof moves outside the
measured main tree. The existing 17-effective-line, six-example statement probe
is reused unchanged. No minimality or build-speed claim is made.

## Acceptance

All nine gates pass: warning-free full source build of 1,803 main modules
(10,511 Lake jobs), both public literal/axiom checks, unchanged internal-strengthening
contracts, five named-module kernel replays and script tests (115 passes and
one optional full-export fixture skip). Replays cover `Goldbach.Theorem`,
`Goldbach.Checks`, `Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks` and
`Goldbach.All` over rebuilt imports; replay of every imported module is not claimed.
All 1,809 main source/configuration/checker pins and the separately pinned probe
match after each gate. The main source inventory is unchanged.

The complete census preserves all 10,408 old public names/kinds/type hashes,
with no missing names or mismatches. The promoted cardinality name alone is added,
bringing the count to 10,409. Its old private statement matches the new public
statement exactly by kind/type hash. Compiled reference cones verify every
consumer and the intended Mathlib/canonical/WF dependency directions.
Four complete-file prototypes passed warning-as-error compilation before application;
source and log fingerprints match. The rounded-prefix consumer prototype contains
the actual promoted proof rather than a forward assumption. Full production
combination acceptance is separate from these historical prototype receipts.

All six public endpoints retain their literal statements, constants and quantifier
order: `D19`, prime conditions, `r^10 ≤ q^9`, the genuine real exponent, Liu's
singular series, strict `1/2500`, fixed `κ < 515093/800000000` before the threshold
and Chen's `0.67`. Public axioms remain only `propext`, `Classical.choice` and
`Quot.sound`. The final producer guard, numerical grids, precision, error constants
and release checks are unchanged. Fresh Blueprint extraction, local rendering,
source positions, graph, annotations and tests pass: 68 nodes,
120 edges, four chapters and all six original exits.

This is an uncommitted local snapshot. Separate concurrent `research/wu2008`
work and its documentation are outside this phase. Historical source-size cohorts
remain separate from current totals.

See [validation](../research/liliu-finite-prefix-cleanup/validation.json),
[pinned inputs](../research/liliu-finite-prefix-cleanup/validation-inputs.json),
[type preservation](../research/liliu-finite-prefix-cleanup/type-preservation.json),
[four-file changes](../research/liliu-finite-prefix-cleanup/changes.json),
[private promotion](../research/liliu-finite-prefix-cleanup/private-proof-redirects.json),
[actual proof references](../research/liliu-finite-prefix-cleanup/shared-proof-references.json),
[complete source fidelity](../research/liliu-finite-prefix-cleanup/source-fidelity.json),
[closure membership](../research/liliu-finite-prefix-cleanup/scope-membership.json),
[source sizes](../research/liliu-finite-prefix-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-finite-prefix-cleanup/blueprint-validation.json).

```sh
python3 research/liliu-finite-prefix-cleanup/reproduce.py --output /tmp/liliu-finite-prefix-recheck
python3 research/liliu-cleanup/measure_main.py
```

Use a new output directory. Default checks cover the main tree only;
`--include-wu` requests separate checks of a stable rebuilt Wu tree.

## Fresh follow-up sweep

A new read-only census of the rebuilt 1,803 main modules scans the current
1,432-module Li–Liu closure for identical and converse Eq/Iff statement hashes
with proof bodies of at least five effective lines, then checks actual compiled
reference directions. It finds no further independent acyclic replacement in
these patterns. Remaining matches depend on the proof they would replace. A
separate scan for explicit private proofs with no incoming stored references, one
source identifier occurrence and no preceding attribute block finds no candidate.
The known converse prefix pair supplies a positive control for the observer.
These limited scans do not establish global proof minimality. See the
[follow-up evidence](../research/liliu-finite-prefix-cleanup/followup-scan.json).
