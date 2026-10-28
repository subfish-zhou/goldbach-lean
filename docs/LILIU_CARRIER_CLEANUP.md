# Li–Liu: carrier identities, analytic growth and finite fibers

This phase starts from the [accepted local-product snapshot](LILIU_PRODUCT_CLEANUP.md):
1,802 main modules / 202,626 effective lines, a 195,071-line Li–Liu closure and
a 99,224-line Chen closure. Thirteen existing main modules change. No production
module or auxiliary Lean probe is added. All original public declaration names,
kinds and type hashes are retained, including the two public scale-membership
proofs moved to their upstream provider.

## Mathematical changes

Four exact prime-carrier filter identities are shared in
[ClosedTriples](../MathlibNt/SieveTheory/LiLiuGoldbachClosedTriples.lean).
Two existing proofs become public; two other proofs move from WeightInitial.
WeightInitial and WeightTriplePartition call these proofs instead of retaining
copies. The distinction between closed and half-open endpoints, singleton
diagonals, the original primality and nondivisibility conditions, `b ≤ c`
and `z ≤ b` are all retained. No boundary contribution is dropped.

The existing real estimate `K * (1 + log x)^B * x^b ≤ x^d` for `K ≥ 0` and
`b < d` moves to [LogPowerBounds](../MathlibNt/Analysis/LogPowerBounds.lean).
The old public beta-payment theorem remains an exact specialization; the private
large-GCD copy is deleted and every call uses the shared estimate. Natural log
powers and real exponents retain their original types. No parameter, sign premise
or eventual quantifier order changes.

The public `wGramPrefix_coordinate_mem_scale` and `wGramPrefix_frequency_mem_scale`
names move from SecondaryRatioBox to the upstream GramResonanceScaleBox, replacing
its two equivalent private proofs. Their public statements are unchanged.
This preserves the original import direction and deletes the downstream copies.
The five independent coordinates, fixed frequency sign, second beta width `F/d`
and positivity conditions recovered from occupied carriers are preserved.

The S4/S5 consumers now use Mathlib's existing
`Finset.card_le_mul_card_image_of_maps_to` with the same maps-to/fiber hypotheses
and the same bound 400. Both private copies are deleted and all five calls are
redirected. The generic Mathlib result orders the factors oppositely; the existing
`mul_comm` normalizations give exactly the previous conclusions, including empty
carriers. A matching canonical type hash with this more general theorem is not
claimed; the complete original consumer statements compile unchanged.

Three `log(log N) / log N → 0` proofs directly compose the established little-o
limit with `log N → ∞`. Explicit `Function.comp_def` simplification is necessary
when the composed function is compared with its lambda form. Two cubic estimates
use `τ² ≤ τ` and its nonnegative multiple. The bounds `0 ≤ τ ≤ 1`, `56τ ≤ δ`
and `8(1+τ)^3 ≤ 8+δ` are exactly the original ones.

| Source group | Net effective-line change |
|---|---:|
| Prime carrier identities and callers | -58 |
| Shared real growth estimate and callers | -16 |
| Scale-membership proof reuse | -32 |
| Three composed logarithmic limits | -13 |
| Two cubic coefficient estimates | -12 |
| Existing finite-fiber bound and callers | -23 |
| Total | -154 |

## Measurements

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main modules | 1,802 | 1,802 | +0 |
| Main effective lines | 202,626 | 202,472 | -154 |
| Li–Liu closure modules | 1,431 | 1,431 | +0 |
| Li–Liu closure effective lines | 195,071 | 194,917 | -154 |
| Chen closure effective lines | 99,224 | 99,246 | +22 |

All shared proof bodies, new public statements, added imports and rewritten callers
are included. Main physical lines change by -157; UTF-8
bytes change by -7,313. The existing 17-line internal-statement
probe is reused unchanged. No production proof is moved outside the measured
main tree, and no auxiliary Lean file is added. Shared dependencies are counted
independently in each theorem closure; closure rows must not be added. External
Lake dependencies remain excluded. No smallest-proof or build-speed claim is made.

Chen's import closure grows by +22 lines because the existing shared
log-power foundation now contains the general real-growth proof. This is included
in the measurement; the complete main tree still saves 154 lines.
Separate concurrent Wu research sources and numerical certificates are excluded.

## Acceptance

All nine gates pass: the complete warning-free 1,802-module build
(10,510 Lake jobs), both public literal/axiom probes, the unchanged internal
strengthening probe, five named-module kernel replays and the script suite
(115 passes, one optional full-export fixture skip). The replays cover
`Goldbach.Theorem`, `Goldbach.Checks`, `Goldbach.OnePlusOneNine`,
`Goldbach.OnePlusOneNineChecks` and `Goldbach.All` over rebuilt imports;
separate replays of every imported module are not claimed.

All 1,808 main source/configuration/checker fingerprints and the separately pinned
existing statement probe match after every gate. The complete census preserves
all 10,394 original public names and kind/type hashes. Only four shared
carrier identities and the general growth estimate are added. The two moved
public Gram names are retained with the same types and verified upstream owners.
Private and specified generated names are excluded from the public comparison.

Thirteen old private declaration names disappear. Eleven replacement statements
have matching original kind/type hashes; two finite-fiber replacements use the
existing more general Mathlib theorem as described above. All previous compiled
consumers of these private names were confined to their own provider modules,
all local calls are redirected, and the full build passes. Some original proofs
are exposed or moved, so this is not a claim of thirteen independently redundant
proof bodies. All thirteen full-file prototypes also passed warning-as-error
compilation before production application. Three initial composition prototypes
failed without explicit composition simplification; those corrected consumers
were recompiled before application. No acceptance relies on a failing draft.

All six public endpoints retain their exact constants and quantifier order:
`D19`, the original prime conditions, `r^10 ≤ q^9`, Liu's singular series, strict `1/2500`,
fixed `κ < 515093/800000000` before the threshold, the exact real exponent
and Chen's `0.67` count. The three unconditional internal Euler positivity
interfaces are rechecked. Public axiom probes use only `propext`,
`Classical.choice` and `Quot.sound`; no release, reachability or numerical
check is weakened. All grids and precision are preserved.

The freshly extracted and locally rendered Blueprint has 68 nodes,
120 edges, four chapters and all six original exits, with matching source
positions. This is an uncommitted local snapshot, not a deployment.

The historical 2026-10-24 cohort table in [SOURCE_SIZE](SOURCE_SIZE.md) had been
incorrectly overwritten by later whole-main totals. It is restored from the
record at checkout HEAD: 7,704 → 7,575 effective lines, 8,999 → 8,908 physical
lines and 609,046 → 600,085 bytes. The current whole-tree table is updated
separately; this documentation correction contributes no proof-code saving.

See [validation](../research/liliu-carrier-cleanup/validation.json),
[pinned inputs](../research/liliu-carrier-cleanup/validation-inputs.json),
[type preservation](../research/liliu-carrier-cleanup/type-preservation.json),
[thirteen-file changes](../research/liliu-carrier-cleanup/changes.json),
[private redirects](../research/liliu-carrier-cleanup/private-proof-redirects.json),
[moved public proofs](../research/liliu-carrier-cleanup/moved-public-proofs.json),
[source sizes](../research/liliu-carrier-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-carrier-cleanup/blueprint-validation.json) and
[follow-up scan](../research/liliu-carrier-cleanup/followup-scan.json).

```sh
python3 research/liliu-carrier-cleanup/reproduce.py --output /tmp/liliu-carrier-recheck
python3 research/liliu-cleanup/measure_main.py
```

Use a new output directory. The default checks cover the main tree only;
`--include-wu` explicitly requests separate checks of a stable rebuilt Wu tree.
Further exact finite-bound duplicates remain under review; no saving from
unimplemented candidates is counted here.
