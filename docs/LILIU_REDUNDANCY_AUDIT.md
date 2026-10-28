# Li–Liu 1+1.9: original-paper comparison and simplification audit

This is the historical read-only audit of the pre-cleanup working tree. Its
sizes are candidate areas, not achieved reductions. See the
[implemented cleanup](LILIU_CLEANUP.md) for the subsequent changes and acceptance. The baseline is the [accepted paper-follow-up snapshot](../research/chen-paper-audit/validation.json),
with 2,143 main modules and 233,959 effective code lines. `c4e1b8d0` identifies
the checkout base; the [source fingerprints](../research/liliu-audit/source-inputs.json)
identify the measured uncommitted sources.

The original source is Li–Liu, [arXiv:2606.05224v1](https://arxiv.org/html/2606.05224v1).
The [paper record](../research/liliu-audit/paper.json) fingerprints the retrieved
HTML; its full text remains local. The comparison concentrates on Theorem 1.1,
(4.18), Sections 5.1–5.5 and the distribution input in Lemma 3.5. It does not
claim a recursive audit of the bibliography.

## What is being preserved

The paper closes its proof with a quantitative count in Section 5.5. The
project exposes four endpoints: natural-power and real-power existence, the
strict `0.0004` distinct-prime count, and its stronger fixed-coefficient family.
All four are the protected targets of the proposed simplification. In
particular, keep the actual distinct-prime count `D19`, `r^10 ≤ q^9`, the Liu
singular-series normalization, and `κ < 515093/800000000` before the threshold.

## Measurements and their limits

The [compiled-reference audit](../research/liliu-audit/analysis.json) reads type,
proof/value and recursor references from all 2,143 current main objects. Each
endpoint census is restricted to its actual import closure. External library
declarations are leaves; generated equation variants conservatively union their
stored references. There are no unresolved local references from the Li–Liu
endpoints.

| Measured area | Modules | Effective code lines |
|---|---:|---:|
| Current Li–Liu import closure | 1,521 | 219,749 |
| Imports shared with Chen | 516 | 97,758 |
| Li–Liu imports outside Chen's closure | 1,005 | 121,991 |
| Modules containing references reached by either existence endpoint | 1,328 | 203,247 |
| Modules containing references reached by either quantitative endpoint | 1,360 | 205,976 |
| Existing existence route's exclusive provider modules | 26 | 1,322 |
| Imported modules with no reached ordinary declaration from the four endpoints | 135 | 12,451 |
| Li–Liu-named subset of that last row | 63 | 4,959 |
| Li–Liu-named modules outside the supported public/check/Blueprint import roots | 262 | 9,859 |

Every line total counts whole source modules, including their unused declarations.
These are not sizes of minimal proof terms. The rows overlap and must not be
added. The 135-module row includes Chen-specific material that remains needed
by Chen. Unreached modules can still supply notation, instances, tactics or
other library consumers, so this census alone does not authorize deleting them.

## Priority 1: one count route for all four endpoints

The [existence assembly](../MathlibNt/SieveTheory/LiLiuGoldbachOneNineUnconditional.lean)
uses the older positive-margin route and the uniform G11 estimate. The
[quantitative assembly](../MathlibNt/SieveTheory/LiLiuGoldbachG11AuthorQuantitative.lean)
uses the stronger author-G11 route. Both ultimately concern the same `D19`.

[The isolated prototype](../research/liliu-audit/experiments/CountToExistence.lean)
proves natural-power existence directly from the accepted strict count via
`D19_pos_iff`. Its real-power counterpart uses the existing exact exponent
bridge. Both compile without an additional analytic premise, and their axiom
reports contain only `propext`, `Classical.choice` and `Quot.sound`.

This makes the older uniform-G11 positivity route a concrete cleanup target.
Its exclusive provider region is 26 modules / 1,322 lines. That is an audit
boundary, not a promised deletion: it includes the 29 lines of the exact
exponent-conversion modules, which the real-power interface still needs.

There is a real implementation dependency to untangle. The quantitative file
currently imports the old existence file for the certified G67 integral bound.
Move the shared numerical certificates into a lower module first, then let the
existence assembly consume the quantitative result. Simply importing the count
assembly back into its current prerequisite would create an import cycle.

## Priority 2: retain one analytic certificate per integral

Two retained-endpoint files explicitly duplicate their predecessors' private
polynomial, derivative, change-of-variable and integration proofs:

| Integral | Earlier certificate | Retained certificate |
|---|---|---|
| S4 / I8 | 160-line module (`MathlibNt/SieveTheory/LiLiuGoldbachS4IntegralScalar.lean`, retired): `8 I8 ≤ 60962/100000` | [Retained proof](../MathlibNt/SieveTheory/LiLiuGoldbachS4RetainedEndpoints.lean): `8 I8 ≤ 60961168/100000000` |
| B10 / I10 | 261-line module (`MathlibNt/SieveTheory/LiLiuGoldbachB10IntegralScalar.lean`, retired): `8 I10 ≤ 540996/100000` | [Retained proof](../MathlibNt/SieveTheory/LiLiuGoldbachB10RetainedEndpoints.lean): `8 I10 ≤ 540995781/100000000` |

The retained bounds are stronger. [Two checked one-line derivations](../research/liliu-audit/experiments/StrongToWeak.lean)
recover the old scalar statements by transitivity and exact rational arithmetic.
Separate isolated compilations show that each retained file compiles with its
predecessor import replaced by the actual analytic prerequisites.

Therefore the analytic certificate can be shared, with old bounds retained as
short consequences where needed. The old modules occupy 421 lines; a final
net saving must include the common module, retained count wrappers and all moved
code. Those 421 lines are already inside the 4,959-line candidate area above.
The stronger retained constants must remain: the existing public coefficient
family consumes them.

## Priority 3: prune obsolete intermediate assemblies

The current files retain successive scalar, high-first, positive-prefix,
uniform-G11 and later paper-split/author-G11 assemblies. They are useful audit
history, but many of their conclusions are absent from the final four proof
reference cones. Examples include the earlier S4/B10 scalar chains,
`LiLiuGoldbachWeightUniformRationalConsumed`, the old G11 window route, and
unused Fouvry payment variants.

The proposed route is to keep the actual finite signed-count inequality and
its required source estimates, then compose the final bounds directly. Shared
coefficient definitions should live below alternative proof assemblies. This
also stops a needed definition from importing every obsolete certificate of an
earlier bound.

The [incoming-consumer record](../research/liliu-audit/candidate-consumers.json)
checks other main modules, not just the endpoints. For example,
`LiLiuGoldbachG12BoundarySource` has no incoming stored declaration reference;
several Fouvry variants have references from unreached declarations in otherwise
live modules. Those callers need pruning or replacement before module deletion.
A filename or an empty endpoint-reference count is insufficient by itself.

## Priority 4: consolidate auxiliary checks separately

There are 262 Li–Liu-named modules outside the supported import roots, totaling
9,859 lines. Name-based classification identifies 222 audit/check/inspection
files (7,700 lines) and 40 other proof/alternative files (2,159 lines).
The classification is a review aid, not a manual finding that every check is
unnecessary.

Repeated declaration dumps, local axiom reports and overlapping production
inspections can be consolidated around the final literal/axiom probes and the
meaningful dependency-cone checks. Keep their regression purpose explicit.
Removing files already outside the endpoint closure reduces shipped/build
source, not the current 219,749-line theorem import closure.

Together, the Li–Liu-named candidates in the three disjoint regions (exclusive
existence providers, unreached imported modules, and modules outside supported
roots) span 349 modules / 16,108 lines. This is a **gross review pool**, including
needed conversion helpers and useful checks, not an estimate of net deletions.

## Additional mathematical sharing

[Chen's continuity-at-five proof](../MathlibNt/SieveTheory/Switching/RosserSieveAsymptotics.lean)
and [Li–Liu's continuity-at-33/8 proof](../MathlibNt/SieveTheory/LiLiuGoldbachS1BetaFactorContinuity.lean)
repeat the same inner-integral and primitive-continuity argument. A theorem for
the common open interval can supply both points. An isolated compilation already
checks the Li–Liu file with its broad `SwitchingPrinciple` import narrowed to
`Switching.RosserSieveAsymptotics`; proving the shared continuity theorem is a
further implementation step.

This and the common epsilon/error-threshold bookkeeping are sensible local
refactors. No large saving is assigned to them before implementation.

## Analytic obligations that remain

The current low-G9 and small-prime G11/G12 producers consume the signed,
well-factorable distribution estimate with a Goldbach-scale residue. Lemma 3.5
is a distinct distribution input, not ordinary BV with renamed parameters.
The [actual rectangle theorem](../MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuFouvryKGoldbachRectangle.lean)
shows the scale, residue, coprimality and uniformity obligations being used.
Its unused auxiliary variants are review candidates; its active analytic proof
has not been shown dispensable.

Likewise, preserve the proved corrected G10 count, repeated-factor and boundary
payments, and the low/high split's actual kernels. The current
[correspondence ledger](../website/report/index.html) records these distinctions.
Paper-level abbreviations do not establish that the formal correction terms
can be dropped.

## Verification and reproduction

[Five isolated compilations pass](../research/liliu-audit/experiment-validation.json):
count-to-existence in both syntaxes; stronger-to-weaker scalar implications;
S4 without the old scalar import; B10 without that import; and the narrower
continuity import. The first two experiments report only standard classical
axioms. Production source and object fingerprints are unchanged. This audit
creates no new post-cleanup full-build acceptance claim; the previous complete
main acceptance still identifies the unchanged production sources.

From a checkout with the matching full build:

```sh
python3 research/liliu-audit/reproduce.py --output /tmp/liliu-audit-fresh
python3 research/liliu-audit/verify_experiments.py --output /tmp/liliu-experiments-fresh
```

Each output directory must be new. Raw extraction files, transformed copies,
logs and the downloaded article remain local; only the compact reports and
reproduction tools are included here. The next implementation should measure
actual net changes after import rewiring, shared-certificate extraction and
complete endpoint/build/Blueprint checks.
