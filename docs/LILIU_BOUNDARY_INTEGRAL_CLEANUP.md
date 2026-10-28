# Li–Liu: shared boundary-integral and low-positivity proofs

This phase starts from the [accepted finite-helper snapshot](LILIU_FINITE_HELPER_CLEANUP.md):
201,992 main effective lines, a 194,437-line Li–Liu closure and a 99,253-line Chen
closure. Five existing main-library files change. No module, public declaration
or auxiliary Lean probe is added or deleted. All 10,405 original public names,
kinds and type hashes remain.

## Boundary-integral changes

The B9 high-domain and weighted G9 error estimates now directly specialize the
existing `IntegralExcessCover.integral_sub_setIntegral_le_of_excess_cover`.
Each supplies its actual grid/source/unit-box sets, pointwise integrand,
measurability, finite volumes, integrability, local approximation error and finite
cover of the excess. Their repeated indicator sign cases, pointwise majorants
and manual integral-addition chains are removed. The common theorem's source is
unchanged and already lies in the Li–Liu closure. Both new direct imports and all
specialization code are counted.

B9 uses its original three strips: left, bottom and oblique. The pointwise cap is
480, the local error is `1600/n`, and the final public error remains `10000/n`.
Its original exact area formulas, including the step expressions normalized to
`17/(240n)`, `7/(120n)` and `329/(3600n)`, are still used.
Weighted G9 uses its original four strips: left, bottom, oblique and right.
The cap is 1500, local error `20000/n`, and the final bound remains
`30000*(h+1/n)` for every `h ≥ 0`, including zero. The exact oblique-area formula
`(41/318)*h + 1927/(19080n)` and the other original areas are preserved.
Neither boundary widths, grid endpoints nor original numerical precision changes.

Both main integrals, their set-integral identities and all subsequent mesh/width
selection before the prime-size limit remain unchanged. The weighted
`integrable_fouvryG9WeightedScaledSource` public theorem is retained and actually
used through `integrable_indicator_iff`. Each specialization proves the common
integral theorem's hypotheses from the original providers; none becomes a new
assumption. The generic cover may overlap and does not require the source to be
contained in the grid. Finite-vector projections are reduced explicitly, retaining
the original rational expressions for the area rewrites.

Four private proof stages disappear: a local indicator-nonnegativity lemma and a
pointwise majorant in each file. Every old stage has exactly one old incoming
declaration, inside its own provider. No literal type-hash equality between these
specialized statements and the polymorphic common theorem is claimed. Their
role is subsumed in the complete public integral specialization. Both private
unit-box definitions and both private volume statements retain their names and
types. Compiled reference cones verify both common-theorem calls, all seven
original strip-area producers, all original caps/local errors/covers and reuse
of the public scaled-source integrability proof.

## Shared low-integral positivity

The existing public `fouvryG9LowIntegral_nonneg` proof and complete statement move
byte for byte from S5Kernel into RelaxedIntegral, immediately after its single
integral identity. Both consumers already import that provider transitively.
The existing public `fouvryG9KernelBudget_low_nonneg` name remains with its
original full type and directly invokes the same proof. Positivity remains
unconditional; no evenness, mesh or eventual-N hypothesis is introduced.
The source integral and its interval endpoints are unchanged.

## Measurements

| Source group | Net effective-line change |
|---|---:|
| B9 high boundary integral | -54 |
| Weighted G9 boundary integral | -68 |
| Shared existing G9 positivity proof and consumers | -5 |
| Complete phase | -127 |

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main modules | 1,803 | 1,803 | 0 |
| Main effective lines | 201,992 | 201,865 | -127 |
| Li–Liu closure modules | 1,432 | 1,432 | 0 |
| Li–Liu closure effective lines | 194,437 | 194,310 | -127 |
| Chen closure effective lines | 99,253 | 99,253 | 0 |

All calls, direct imports and the moved eight-line positivity proof are counted.
Main physical lines change by -132; UTF-8 bytes by
-6,742. All five modified modules lie outside Chen's import closure,
whose complete module/line/byte totals are unchanged. Shared modules count
independently in each theorem closure. External Lake dependencies are excluded.
No proof moves outside the measured main tree. The existing 17-line internal
statement contract is reused without any new auxiliary Lean code. No minimality
or build-speed claim is made.

## Acceptance

All nine gates pass: warning-free 1,803-module full source build (10,511 Lake jobs),
both public literal/axiom checks, unchanged internal-strengthening contracts,
five named-module kernel replays and script tests (115 passes and one optional
full-export fixture skip). Kernel replays cover `Goldbach.Theorem`,
`Goldbach.Checks`, `Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks` and
`Goldbach.All` over rebuilt imports; independent replay of every imported module
is not claimed. All 1,809 main source/configuration/checker pins and the separately
pinned statement probe match after each gate. The inventory is unchanged.
The complete census preserves all 10,405 old public names/kinds/type hashes,
with no missing or added public declarations.

All five complete-file prototypes passed warning-as-error compilation before
application; matching source/log fingerprints were rechecked. Positivity consumer
prototypes include the actual moved proof, not a forward assumption. Initial
boundary drafts needed explicit unit-box unfolding and finite-vector head/tail
reductions; a first weighted draft encountered a missing object during a source
rebuild. The final successful complete drafts ran over stable objects only after
that full build passed. No failed draft supplies accepted evidence. The complete
production import combination is checked separately by this phase's full build.

All six public endpoints retain their exact constants and quantifier order:
`D19`, prime conditions, `r^10 ≤ q^9`, the genuine real exponent, Liu's singular
series, strict `1/2500`, fixed `κ < 515093/800000000` before the threshold and
Chen's `0.67`. Public axioms remain only `propext`, `Classical.choice` and
`Quot.sound`. The final producer guard, original numerical grids, precision,
error constants and release checks are unchanged. Fresh Blueprint extraction,
local rendering, source positions, graph, annotations and tests pass:
68 nodes, 120 edges, four chapters and all six original exits.

This is an uncommitted local snapshot. Separate concurrent `research/wu2008`
sources, certificates and documentation are outside this phase. Historical
source-size cohorts remain separate from current totals.

See [validation](../research/liliu-boundary-integral-cleanup/validation.json),
[pinned inputs](../research/liliu-boundary-integral-cleanup/validation-inputs.json),
[type preservation](../research/liliu-boundary-integral-cleanup/type-preservation.json),
[five-file changes](../research/liliu-boundary-integral-cleanup/changes.json),
[removed private stages](../research/liliu-boundary-integral-cleanup/removed-private-proofs.json),
[retained private data](../research/liliu-boundary-integral-cleanup/retained-private-statements.json),
[moved public positivity proof](../research/liliu-boundary-integral-cleanup/moved-public-proofs.json),
[actual shared-proof references](../research/liliu-boundary-integral-cleanup/shared-proof-references.json),
[source sizes](../research/liliu-boundary-integral-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-boundary-integral-cleanup/blueprint-validation.json).

```sh
python3 research/liliu-boundary-integral-cleanup/reproduce.py --output /tmp/liliu-boundary-integral-recheck
python3 research/liliu-cleanup/measure_main.py
```

Use a new output directory. Default checks cover the main tree only;
`--include-wu` requests separate checks of a stable rebuilt Wu tree.
Unimplemented follow-up candidates are excluded from the savings above.
