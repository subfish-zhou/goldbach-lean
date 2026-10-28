# Li–Liu: one shared quartic-log remainder payment

This phase starts from the [accepted boundary-integral snapshot](LILIU_BOUNDARY_INTEGRAL_CLEANUP.md):
201,865 main effective lines, a 194,310-line Li–Liu closure and a 99,253-line Chen
closure. Three existing main-library files change. No module or auxiliary Lean
probe is added. All 10,405 old public names/kinds/type hashes remain. One new
public shared helper replaces two identical private proofs.

## Proof change

`LiuWeight.quartic_log_error_absorb_eventually` lives in the existing canonical
Arithmetic.LiuLogScaleAbsorption provider. Its statement is exactly the old
B10/S2 private statement: for positive real `C` and `δ`, there exists a natural
`N₀ ≥ 4` such that every `N ≥ N₀` satisfies
`C*N/log(N)^(4:Real) ≤ δ*liuUniversalProduct*N/log(N)^(2:Real)`.
Both old private kinds/type hashes match this shared theorem. The complete
proof is copied from B10, preserving the absolute-value envelope, specialization
of the general logarithmic-remainder bound and cutoff `max 4 M`.
The coefficient and relative error remain fixed before the natural threshold;
the varying `N` remains after it. No sign, exponent or threshold assumption is
weakened or strengthened.

B10 and S2 remove their private copies, replace their direct log-absorption import
with the canonical Liu provider and call the shared name. Each old private helper
had exactly one incoming declaration inside its own provider and no outside
consumer. Actual compiled reference cones verify that both original normalized
upper-bound producers now reach the common theorem and that the theorem reaches
the unchanged general logarithmic-remainder producer. All original public
normalized bounds retain their full types, including their independently varying
parameters, main masses and original normalization constants.

The canonical provider's original inverse-log theorem for the genuine
N-dependent Liu singular series is source-identical and has the same normalized
compiled-reference record. The new quartic payment targets the constant universal
product appearing in the original two private statements; it does not replace the
separate genuine-singular-series theorem or identify the two quantities.

## Measurements

| Source | Effective lines before → after | Change |
|---|---:|---:|
| Canonical Liu log-payment provider | 19 → 35 | +16 |
| B10 normalized upper consumer | 360 → 344 | -16 |
| S2 normalized upper consumer | 514 → 498 | -16 |
| Complete phase | 893 → 877 | -16 |

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main modules | 1,803 | 1,803 | 0 |
| Main effective lines | 201,865 | 201,849 | -16 |
| Li–Liu closure modules | 1,432 | 1,432 | 0 |
| Li–Liu closure effective lines | 194,310 | 194,294 | -16 |
| Chen closure effective lines | 99,253 | 99,269 | +16 |

All 16 shared-provider lines, imports and rewritten calls are counted. Main
physical lines change by -16; UTF-8 bytes by -733.
The canonical provider is already imported by Chen, so its complete source closure
grows by 16 lines. Both changed B10/S2 consumers lie outside that closure. Actual
compiled references confirm that neither `Goldbach.chen_theorem` nor
`Goldbach.representation_lower_bound` reaches the new quartic helper. The Chen
source-closure growth is fully reported and is not a change to its final theorem,
assumptions or `0.67` constant. Keeping the related payments in their existing
canonical provider avoids creating a small application-only module.

Shared modules count independently in each theorem closure. External Lake
dependencies are excluded. No proof moves outside the measured main tree.
The existing 17-line internal-statement probe is reused unchanged; no auxiliary
Lean code is added. No minimality or build-speed claim is made.

## Acceptance

All nine gates pass: warning-free 1,803-module full source build (10,511 Lake jobs),
both public literal/axiom checks, unchanged internal-strengthening contracts,
five named-module kernel replays and script tests (115 passes and one optional
full-export fixture skip). Replays cover `Goldbach.Theorem`, `Goldbach.Checks`,
`Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks` and `Goldbach.All`
over rebuilt imports; independent replay of every imported module is not claimed.
All 1,809 main source/configuration/checker pins and the separately pinned
statement probe match after each gate. The inventory is unchanged.

The complete census preserves all 10,405 old public names/kinds/type hashes,
with no missing public declarations. Only the shared quartic theorem is added,
bringing the public count to 10,406. Both old private statements have exactly
its kind/type hash; the two original public consumers actually reach it.
All three complete-file prototypes passed warning-as-error compilation before
application; matching source/log hashes were checked. Consumer prototypes include
the actual shared proof rather than a forward assumption. The complete production
import combination is accepted separately by the full build.

All six public endpoints retain their exact constants and quantifier order:
`D19`, original prime conditions, `r^10 ≤ q^9`, the genuine real exponent, Liu's
singular series, strict `1/2500`, fixed `κ < 515093/800000000` before the threshold
and Chen's `0.67`. Public axioms remain only `propext`, `Classical.choice` and
`Quot.sound`. The original final producer guard, numerical grids, precision,
error constants and release checks are unchanged. Fresh Blueprint extraction,
local rendering, source positions, graph, annotations and tests pass:
68 nodes, 120 edges, four chapters and all six original exits.

This is an uncommitted local snapshot. Separate concurrent `research/wu2008`
sources, certificates and documentation are outside this phase. Historical
source-size cohorts remain separate from current totals.

See [validation](../research/liliu-quartic-log-cleanup/validation.json),
[pinned inputs](../research/liliu-quartic-log-cleanup/validation-inputs.json),
[type preservation](../research/liliu-quartic-log-cleanup/type-preservation.json),
[all source changes](../research/liliu-quartic-log-cleanup/changes.json),
[exact private replacements](../research/liliu-quartic-log-cleanup/private-proof-redirects.json),
[retained inverse-log proof](../research/liliu-quartic-log-cleanup/retained-inverse-log-proof.json),
[actual shared-proof references](../research/liliu-quartic-log-cleanup/shared-proof-references.json),
[closure membership](../research/liliu-quartic-log-cleanup/scope-membership.json),
[source sizes](../research/liliu-quartic-log-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-quartic-log-cleanup/blueprint-validation.json).

```sh
python3 research/liliu-quartic-log-cleanup/reproduce.py --output /tmp/liliu-quartic-log-recheck
python3 research/liliu-cleanup/measure_main.py
```

Use a new output directory. Default checks cover the main tree only;
`--include-wu` requests separate checks of a stable rebuilt Wu tree.
Unimplemented follow-up candidates are excluded from the savings above.
