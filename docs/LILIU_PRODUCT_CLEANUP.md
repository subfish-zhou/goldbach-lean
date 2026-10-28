# Li–Liu: uniform local products and normalized error payments

This phase starts from the [accepted shared-lemma snapshot](LILIU_SHARED_LEMMA_CLEANUP.md):
1,801 main modules / 202,818 effective lines, a 195,263-line Li–Liu closure and
a 99,235-line Chen closure. Nine existing files change and one shared production
module is added. Five private declarations are removed together with redirecting
all their calls. Every original public declaration name and type is retained.

## Mathematical changes

The new [S1 local-product module](../MathlibNt/SieveTheory/LiLiuGoldbachS1LocalProduct.lean)
provides one uniform witness formerly proved independently by the beta lower-density,
level-six lower-density and S3 upper-density consumers. Its statement fixes `K > 1`
before every `N`, evenness proof, interval parameter and cutoff. The actual
`goldbachS1BoundingSieve` and restricted prime product remain unchanged.

The proof still uses the established Mertens inverse-interval bound. The existing
prime-factor-set identity supplies primality and nondivisibility directly;
evenness excludes the prime two. The selected interval membership comes directly
from the filter. This removes the repeated detour through prime-factor membership,
divisibility of the product and a separate reconstruction of the same filter.
All three old private witness proofs are deleted and their consumers call the
shared theorem directly. Its canonical type hash matches all three old private
statements, preserving the full uniform quantifier order.

Three paid-error proofs for B8, B9 high-first and the G11 normalized integral
specialize the existing `Analysis.LogScaleAbsorption` theorem with logarithmic
saving one and normalization exponent two. The established positive lower bound
for Liu's singular series supplies the same normalization as before. Coefficients
may have either sign; tolerance positivity and eventual-threshold order are
preserved. The original power-three remainder and power-two main term are unchanged.

The paper-Q prime-factor-product identity now uses `Nat.primeFactors_prod`
instead of duplicating its induction. Two private interval-maximum nonnegativity
proofs are deleted, and their B10/S2 consumers call the existing general
`liuMainPanCoprimeIntervalMaxL_nonneg` theorem. The original empty-residue case
and all interval parameters remain covered. No assumption or numerical bound
is changed by these replacements.

## Measurements

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main modules | 1,801 | 1,802 | +1 |
| Main effective lines | 202,818 | 202,626 | -192 |
| Li–Liu closure modules | 1,430 | 1,431 | +1 |
| Li–Liu closure effective lines | 195,263 | 195,071 | -192 |
| Chen closure effective lines | 99,235 | 99,224 | -11 |

All 37 effective lines of the new module, added imports and rewritten callers
are included. Main physical lines change by -188; UTF-8
bytes change by -8,612. No production proof is moved
outside the measured main tree. The preceding phase's 17-line internal-statement
probe is reused unchanged; this phase adds no auxiliary Lean probe. Thus the
phase's Lean-source saving, counting all newly added Lean files, is also
192 lines. Shared dependencies are counted independently in each theorem
closure; the closure rows must not be added. External Lake dependencies are
excluded by the existing rule. No smallest-proof or controlled speedup is claimed.

## Acceptance

The complete warning-free 1,802-module build passes 10,510 Lake jobs.
All nine gates pass: the full source build, both public literal/axiom probes,
the preceding internal-strengthening probe, five named-module kernel replays
and the script suite (115 passes, one optional full-export fixture skip).
The replays cover `Goldbach.Theorem`, `Goldbach.Checks`, `Goldbach.OnePlusOneNine`,
`Goldbach.OnePlusOneNineChecks` and `Goldbach.All` over rebuilt imports;
separate replays of every imported module are not claimed.

All 1,808 main source/configuration/checker fingerprints and the separately pinned
existing statement probe match after each gate. The complete census preserves
all 10,393 original public kinds/type hashes, with no missing
names or changed types. Only the shared uniform local-product theorem is added.
Private and specified generated names are excluded from that public comparison.
The five deleted private statements are checked against their actual replacement
kind/type hashes. Their previous compiled consumers were confined to their own
source modules, all local calls are redirected, and the complete build passes.

All six public endpoints retain their original constants and quantifier order:
`D19`, `r^10 ≤ q^9`, Liu's singular-series normalization, the strict `1/2500`
count, fixed `κ < 515093/800000000` before the threshold, the exact real exponent
and Chen's `0.67` count. The preceding three unconditional internal Euler
positivity statements are independently rechecked. Public axiom probes allow
only `propext`, `Classical.choice` and `Quot.sound`. No release or proof-reachability
check is weakened, and all source grids and numerical precision are preserved.

The freshly extracted and locally rendered Blueprint has 68 nodes,
120 edges, four chapters and all six original exits. Source positions match
the extraction. This is an uncommitted local snapshot, not a deployment.
Separate concurrent Wu research sources and numerical certificates are excluded.

See [validation](../research/liliu-product-cleanup/validation.json),
[pinned inputs](../research/liliu-product-cleanup/validation-inputs.json),
[type preservation](../research/liliu-product-cleanup/type-preservation.json),
[ten-file changes](../research/liliu-product-cleanup/changes.json),
[private-proof redirects](../research/liliu-product-cleanup/private-proof-redirects.json),
[source sizes](../research/liliu-product-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-product-cleanup/blueprint-validation.json).

```sh
python3 research/liliu-product-cleanup/reproduce.py --output /tmp/liliu-product-recheck
python3 research/liliu-cleanup/measure_main.py
```

Use a new output path. The default queue checks the main tree only;
`--include-wu` explicitly requests independent checks of a stable rebuilt Wu tree.
Further duplicate private geometric and growth estimates remain under review;
no saving from unimplemented candidates is counted here.
