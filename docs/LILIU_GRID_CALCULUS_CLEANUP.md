# Li–Liu: finite weighted-cell calculus and shared convergence

This phase starts from the [accepted shared-foundation snapshot](LILIU_LOG_KERNEL_CLEANUP.md):
1,801 main modules / 202,991 effective lines, a 195,401-line Li–Liu import
closure and a 99,248-line Chen closure. Nine existing files change; no module,
original public declaration or import from the compatibility facade is removed.

## Mathematical simplifications

Three general lemmas in [LogGridEstimates](../MathlibNt/Analysis/LogGridEstimates.lean)
replace repeated integration and convergence arguments:

* `integrable_weighted_sum` proves integrability of a finite sum of weighted
  cell indicators from integrability of the actual density on each measurable
  selected cell.
* `integral_weighted_sum` identifies its integral with the sum of the actual
  weighted cell integrals. It allows arbitrary real coefficients and overlapping
  cells; it introduces no partition or density-normalization assumption.
* `tendsto_of_sub_le_div_nat` derives convergence along positive mesh sizes from
  the original lower bound and an actual `C/n` error bound. The original limit
  and error constant remain parameters.

The two integration lemmas are used by the canonical Liu grid, B8, B10, the
B9 high-first grid and the four-dimensional G11/G12 meshes. Their original
per-cell logarithmic mass identities, measurable sets, integrability proofs,
selected cells, coefficients and density functions remain the inputs.
The canonical Liu and B10 limit theorems specialize the third lemma with their
unchanged `759/n` and `260/n` error bounds.

B9 density continuity and reciprocal bounds specialize the preceding phase's
rectangle lemmas. B9 high-first oblique-strip volume specializes the existing
`volume_strip` theorem; its original base, width and exact numerical expression
are retained. Its public section identity also remains available. Selected-cell
values and zero-outside-region proofs reuse the existing finite weighted-sum
lemmas, and B8/B9 reuse the existing weighted error estimate.

The empty aggregate-character compatibility module retains every original
import command, in the original order. It loses seven local open/namespace
commands and stale empty proof headings, including obsolete claims that analytic
regimes remained open. No theorem is removed from that facade.

## Net measurements

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main effective lines | 202,991 | 202,902 | -89 |
| Li–Liu closure effective lines | 195,401 | 195,347 | -54 |
| Chen closure effective lines | 99,248 | 99,252 | +4 |

All three added lemmas and the explicit Mathlib import are included. Main
physical lines change by -122 and UTF-8 bytes by
-2,845. Main, Li–Liu and Chen module counts remain
1,801, 1,430 and 528, respectively.
The smaller Li–Liu saving reflects that the retained canonical Liu module and
compatibility facade are already outside its import closure. Chen's shared
foundation growth and canonical-proof saving are both counted.
External Lake dependencies are excluded by the same rule as the preceding reports.
No smallest-proof or controlled build-time comparison is claimed.

## Acceptance

The complete warning-free 1,801-module build passes all 10,509 Lake jobs. Both
public literal/axiom probes, the five independent named-module kernel replays
and the script suite pass (115 passes, one optional full-export fixture skip).
The replays cover `Goldbach.Theorem`, `Goldbach.Checks`, `Goldbach.OnePlusOneNine`,
`Goldbach.OnePlusOneNineChecks` and `Goldbach.All` over the rebuilt imports;
separate replays of every imported module are not claimed. All 1,807 pinned
source/configuration/checker inputs match after every gate.

All 10,389 original public declaration
kinds/type hashes match the preceding complete census; none are missing.
Only the three generic calculus lemmas are added. Private and specified generated
names are excluded. The six original Chen/Li–Liu endpoint statements retain
`D19`, `r^10 ≤ q^9`, the Liu singular-series normalization, the strict `1/2500`
count, fixed `κ < 515093/800000000` before the threshold, the exact real exponent
and Chen's `0.67` count. All source grids, numerical precision and error constants
are retained. Public axiom probes allow only `propext`, `Classical.choice` and
`Quot.sound`; no release or proof-reachability check is weakened.

The newly extracted and locally rendered Blueprint has 68 nodes,
120 edges, four chapter graphs and all six original public exits.
Source positions match the fresh extraction. This is an uncommitted local snapshot,
not a publication or deployment. Separate concurrent Wu research sources and
numerical certificates remain outside this main acceptance.

See the [validation](../research/liliu-grid-calculus-cleanup/validation.json),
[pinned inputs](../research/liliu-grid-calculus-cleanup/validation-inputs.json),
[type comparison](../research/liliu-grid-calculus-cleanup/type-preservation.json),
[nine-file changes](../research/liliu-grid-calculus-cleanup/changes.json),
[facade import preservation](../research/liliu-grid-calculus-cleanup/compatibility-facade.json),
[source sizes](../research/liliu-grid-calculus-cleanup/source-size.json),
[standalone probes](../research/liliu-grid-calculus-cleanup/standalone-probes.json) and
[Blueprint evidence](../research/liliu-grid-calculus-cleanup/blueprint-validation.json).

```sh
python3 research/liliu-grid-calculus-cleanup/reproduce.py --output /tmp/liliu-grid-calculus-recheck
python3 research/liliu-cleanup/measure_main.py
```

Use a new output path. The default queue checks the main tree only;
`--include-wu` explicitly requests independent checks of a stable rebuilt Wu tree.
A [follow-up scan](../research/liliu-grid-calculus-cleanup/followup-scan.json)
records a fully compiled finite-indicator Abel prototype. Counting its auxiliary
lemmas, its cohort grows from 81 to 97 effective lines, so it is not adopted.
The scan of all 1,801 compiled module inventories finds no remaining declaration-free
facades containing only imports plus removable local open/namespace/section/end
commands. This limited scan does not establish mathematical minimality. Further
reuse in the piecewise-FTC argument and grid geometry remains under analysis;
no saving from those candidates is counted here.
