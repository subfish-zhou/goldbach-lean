# Li–Liu: shared logarithmic coordinates and harmonic foundations

This phase starts from the [accepted continuity follow-up](LILIU_CONTINUITY_CLEANUP.md):
1,799 main modules / 203,002 effective lines, and a 1,435-module / 196,487-line
Li–Liu import closure. It adds two shared foundation modules and deletes none.

## Mathematical and dependency changes

[LiuLogCoordinates](../MathlibNt/SieveTheory/Liu/PrimePairs/LiuLogCoordinates.lean)
owns the three logarithmic-coordinate functions, the rectangle integral identity
and the integrability indicator helper. Their original source blocks are unchanged.
Three general lemmas prove density continuity on positive-coordinate rectangles,
kernel continuity under an upper-corner gap, and the reciprocal density bound.
The original Liu, B8 and B10 regularity/bound proofs specialize those lemmas.
Their integration regions, half-open grids and numerical caps remain unchanged.
The complete original Liu grid selection and convergence proofs remain available.

[LiuWeightHarmonic](../MathlibNt/SieveTheory/Liu/Weights/LiuWeightHarmonic.lean)
collects eight existing definitions and elementary bounds from the Selberg and
aggregate-character modules. All eight source bodies and public names are
preserved. Actual consumers import this lower layer directly. The full Selberg,
convolution and application proofs remain in their original modules.

The full primitive Perron proof now imports its actual Mathlib/PNT providers,
removing an indirect dependency on the complete Liu aggregate application.
Its proof body is unchanged. The original complex C⋆ algebra instance provider
is imported explicitly so that the elaborated public types also remain unchanged.
One consumer calls the underlying character norm
bound directly; the original public wrapper remains available.
The G9 antiderivative proofs explicitly import `MathlibNt.Tactic.ElementaryDeriv`,
which was previously a transitive tactic dependency. Their proof steps are unchanged.

## Measured result

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main modules | 1,799 | 1,801 | +2 |
| Main effective lines | 203,002 | 202,991 | -11 |
| Li–Liu closure modules | 1,435 | 1,430 | -5 |
| Li–Liu closure effective lines | 196,487 | 195,401 | -1,086 |
| Chen closure effective lines | 99,226 | 99,248 | +22 |

Main physical lines change by +6 and UTF-8
bytes by +916. The two added modules and all
moved code are included. The larger Li–Liu closure saving reflects fewer
application imports; it is not a deletion of those retained source proofs.
Chen's shared dependency growth is included explicitly. External Lake dependencies
are excluded by the same measurement rule as the preceding reports.
No minimal-proof or build-time claim is made.

## Acceptance

The complete 1,801-module, 10,509-job warning-free main build passes.
Both public literal/axiom probes and five independent named-module kernel replays
pass: `Goldbach.Theorem`, `Goldbach.Checks`, `Goldbach.OnePlusOneNine`,
`Goldbach.OnePlusOneNineChecks` and `Goldbach.All`. These replays use the rebuilt
imports; separate replays of every imported module are not claimed.
The script suite reports 115 passes and one optional full-export fixture skip.
All 1,807 source/configuration/checker fingerprints match after every gate.

All 10,386 original public declaration
kinds/type hashes match the preceding complete main census; none are missing.
Only the three new generic helpers are added. The
[intermediate type check](../research/liliu-log-kernel-cleanup/intermediate-type-check.json)
records a rejected narrower-import snapshot and its explicit instance-provider
correction; its successful build alone was insufficient for acceptance.
Private and specified generated
names are excluded. All thirteen relocated original public declarations retain
their source bodies. The six protected Chen/Li–Liu endpoints retain all original
constants and quantifiers: `D19`, `r^10 ≤ q^9`, the Liu singular-series
normalization, the strict `1/2500` count, the fixed `κ < 515093/800000000`
before the threshold, the exact real exponent and Chen's `0.67` bound.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed by the public
axiom probes. No check or reachability guard is weakened.

The freshly extracted and locally rendered Blueprint has 68 nodes,
120 edges, four chapters and all six public exits. Source positions
match the extraction. This is an uncommitted working-tree snapshot, not a deployment.
Separate concurrent Wu research sources and numerical certificates are outside
this phase and are untouched by it.

See the [validation](../research/liliu-log-kernel-cleanup/validation.json),
[pinned inputs](../research/liliu-log-kernel-cleanup/validation-inputs.json),
[type comparison](../research/liliu-log-kernel-cleanup/type-preservation.json),
[file changes](../research/liliu-log-kernel-cleanup/changes.json),
[unchanged moved blocks](../research/liliu-log-kernel-cleanup/moved-definitions.json),
[source sizes](../research/liliu-log-kernel-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-log-kernel-cleanup/blueprint-validation.json).

```sh
python3 research/liliu-log-kernel-cleanup/reproduce.py --output /tmp/liliu-foundations-recheck
python3 research/liliu-cleanup/measure_main.py
```

The output path must be new. The main queue excludes the separate Wu tree by
default; `--include-wu` explicitly requests its independent checks against a stable
rebuilt Wu snapshot. The prior rejected 165-module deletion remains rejected and
contributes no savings here. Further common grid-geometry proofs and the B9
regularity specializations remain candidates; their savings are not counted.
