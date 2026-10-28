# Li–Liu: shared continuity, positivity and logarithmic domination

This phase starts from the [accepted finite-cell calculus snapshot](LILIU_GRID_CALCULUS_CLEANUP.md):
1,801 main modules / 202,902 effective lines, a 195,347-line Li–Liu closure and
a 99,252-line Chen closure. Five existing production files change; no module or
existing public declaration name is deleted.

## Mathematical changes

The existing inner-integral continuity lemma in
[DimensionOneLowerFactor](../MathlibNt/SieveTheory/LinearSieve/DimensionOneLowerFactor.lean)
is made public. Its statement and entire proof body are unchanged. The third
upper-interval module reuses it and the already public lower-factor continuity
theorem on `[4,6]`. Both old third-interval names remain available, including
the private inner helper still used later in that file. This replaces two
independent copies of the primitive-integral continuity arguments.

The Fouvry logarithmic-domination wrapper now directly specializes the existing
`MathlibNt.Analysis.eventually_nat_log_rpow_le_rpow` theorem. Its real exponents,
positive-power hypothesis and eventual quantifier are unchanged. The actual
provider is imported explicitly.

For the absolute local Euler correction, summability is already proved for
every `N`. The summand at exponent zero is `|1| = 1`, and all other summands are
nonnegative. `Summable.le_tsum` therefore gives a total at least one directly.
Subtracting one proves nonnegativity without expanding the local factor or
splitting on whether the prime divides `N`.

This removes the unnecessary `Even N` hypothesis from exactly three internal
statements, keeping their names and conclusions:

* `liuSelbergAbsPrimeDeviation_nonneg_core`;
* `liuSelbergAbsPrimeDeviation_nonneg`;
* `liuAbsoluteEulerFactor_one_le`.

They now hold for every natural `N`. Callers supply `N` explicitly where the
removed proof previously determined it. The signed Euler formulas, uniform
summability arguments and original six public Chen/Li–Liu endpoints keep their
original hypotheses, constants and quantifier order. Callers outside this snapshot
which pass the old internal `Even N` argument must use the new argument list.

## Measurements

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main effective lines | 202,902 | 202,818 | -84 |
| Li–Liu closure effective lines | 195,347 | 195,263 | -84 |
| Chen closure effective lines | 99,252 | 99,235 | -17 |

The explicit import and all changed production code are included. Main physical
lines change by -84 and UTF-8 bytes by
-3,593. Module counts remain 1,801 main,
1,430 Li–Liu and 528 Chen. The existing main-source
measurement rule excludes external Lake dependencies and research utilities.

The new standalone acceptance probe contributes another 17 effective Lean lines
in the research audit directory and is not imported by the production proofs.
Counting that new probe as well, the phase's net Lean-source change is
-67 lines. No proof code is moved outside the measured production tree.
No smallest-proof or controlled build-time claim is made.

## Acceptance

The complete warning-free 1,801-module build passes 10,509 Lake jobs. Both public
literal/axiom probes, five independent named-module kernel replays and the script
suite pass (115 passes, one optional full-export fixture skip). The replays cover
`Goldbach.Theorem`, `Goldbach.Checks`, `Goldbach.OnePlusOneNine`,
`Goldbach.OnePlusOneNineChecks` and `Goldbach.All` over rebuilt imports;
separate replays of every import are not claimed.

The additional [statement probe](../research/liliu-shared-lemma-cleanup/StrengthenedStatements.lean)
checks all three unconditional internal statements and all three old-premise
consequences in Lean. The nine-gate reproducer pins this auxiliary file separately
and verifies it together with all 1,807 main source/configuration/checker inputs
after each gate.

The complete census retains all 10,392 original
public names. Kind/type hashes match for 10,389;
the only three type changes are the intentional strengthenings above, checked by
the independent probe. One pre-existing private lemma becomes public, with its
original kind/type hash and proof body preserved. No unexpected kind/type change
is allowed. Private and specified generated names are excluded from the public
comparison. All six public endpoints retain `D19`, `r^10 ≤ q^9`, Liu's
singular-series normalization, the strict `1/2500` count, fixed
`κ < 515093/800000000` before the threshold, the exact real exponent and Chen's
`0.67` count. Public axiom reports allow only `propext`, `Classical.choice` and
`Quot.sound`. No release or proof-reachability check is weakened.

The fresh local Blueprint has 68 nodes, 120 edges, four chapters
and all six original public exits; source locations match the fresh extraction.
This is an uncommitted working-tree snapshot, not publication or deployment.
Separate concurrent Wu research sources and numerical certificates are excluded.

See [validation](../research/liliu-shared-lemma-cleanup/validation.json),
[pinned inputs](../research/liliu-shared-lemma-cleanup/validation-inputs.json),
[type comparison and strengthenings](../research/liliu-shared-lemma-cleanup/type-preservation.json),
[five-file changes](../research/liliu-shared-lemma-cleanup/changes.json),
[unchanged exposed lemma](../research/liliu-shared-lemma-cleanup/exposed-lemma.json),
[source sizes](../research/liliu-shared-lemma-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-shared-lemma-cleanup/blueprint-validation.json).

```sh
python3 research/liliu-shared-lemma-cleanup/reproduce.py --output /tmp/liliu-shared-lemma-recheck
python3 research/liliu-cleanup/measure_main.py
```

Use a new output path. The default queue checks the main tree only;
`--include-wu` explicitly requests independent checks of a stable rebuilt Wu tree.
A follow-up scan including private statements identified further local-product,
normalization and interval-maximum proof duplicates. Those candidates require
separate dependency analysis and kernel checks; no savings from them are counted.
