# Li–Liu: shared low-conductor budgets and Pan maxima

This phase starts from the [accepted endpoint snapshot](LILIU_ENDPOINT_CLEANUP.md):
1,802 main modules / 202,394 effective lines, a 194,839-line Li–Liu closure and
a 99,246-line Chen closure. Eight existing main-library modules change. No
production module or auxiliary Lean probe is added. All original public names,
kinds and type hashes remain. One existing public budget proof moves upstream.

## Mathematical changes

The generic `Wu2004MeanValue.balanced_lowMovingSource_le_budget` statement moves
from BalancedLowSource into LowSource, replacing the equivalent private budget
there. Its duplicate statement and 68-line proof body are deleted downstream.
The complete coefficient sum remains **inside** the norm in `lowMovingSource`;
that definition's source text is unchanged. The endpoint `t(q,χ,a)` remains
independently chosen for every modulus, character and coefficient index.
Conductor one remains excluded by the original `Icc 2 Q` carrier. The generic
budget retains all original sign, support and prefix hypotheses, including
`S ⊆ Icc 1 U`, `U ≤ N`, `N ≥ 3` and the fixed-cofactor coprime-prefix deletion.

The higher estimates are deliberately kept distinct. `low_source_nat_moving`
retains `h ≤ sqrt N` and `U ≤ N^(2/3)`. The balanced natural/real moving estimates
retain `h ≤ N` and `U ≤ N^(1-η)` for every `η > 0`. Their complete public types
are unchanged, and compiled reference cones verify that all three actually use
the shared budget. No balanced range is replaced by the smaller unbalanced range.
All constants and eventual thresholds still precede the varying carriers,
weights and independently moving endpoints as in the original statements.

LowPrefix deletes its private quotient-quarter and parameter proofs and directly
imports the existing PanQuotientBounds provider. The public quarter theorem uses
the shorter, already established proof body, with its original statement intact.
The floor is still the natural quotient `N / a`; the support exponent `2/3`,
quarter exponent `1/4`, logarithmic comparison factor four, arbitrary real `b`
and threshold parameter `M` remain unchanged. The actual maximal SW prefix proof
and every independent prefix `y ≤ N/a` are retained. No additional SW assumption
or frozen-prefix replacement is introduced.

One shared `liuMainPanCoprimeIntervalSum_abs_le_maxL` theorem in the actual Pan
error-envelope provider replaces the private B10/S2 interval-max copies. Its
statement is exactly the old bound for arbitrary `main`, signed `f`, endpoints,
`d ≥ 1` and `Nat.Coprime d N`. The original proof that `N % d` is a unit residue
is inlined once. The finite image is explicit so its index type is determined.
B10 calls it at both `N` and `floor(εN)`; S2 calls it at its original endpoint.
The original support/coprimality conditions and empty-residue nonnegativity
interface are retained. No sign restriction on the coefficient function is added.

The private `squarefree_prod_of_primes` in the literal Jurkat–Richert
specialization retains its name and full finite-prime-set statement. Mathlib's
`Finset.squarefree_prod_of_pairwise_isCoprime`, with coprimality of distinct primes,
replaces the repeated local induction. The empty product remains covered.
The surrounding literal `1/p` density is not identified with the separate
Goldbach `1/(p-1)` density; all Euler/totient identities remain unchanged.

| Source group | Net effective-line change |
|---|---:|
| Shared low-conductor budget and callers | -79 |
| Quotient-quarter/parameter reuse and shorter proof | -60 |
| Shared Pan maximum bound and two consumers | -28 |
| Existing generic squarefree-product proof | -20 |
| Total | -187 |

## Measurements

| Scope | Before | After | Change |
|---|---:|---:|---:|
| Main modules | 1,802 | 1,802 | +0 |
| Main effective lines | 202,394 | 202,207 | -187 |
| Li–Liu closure modules | 1,431 | 1,431 | +0 |
| Li–Liu closure effective lines | 194,839 | 194,652 | -187 |
| Chen closure effective lines | 99,246 | 99,260 | +14 |

All moved proof bodies, the new 19-line public maximum theorem, the added direct
import and rewritten calls are counted. Main physical lines change by
-192; UTF-8 bytes change by -8,882. The existing
17-line internal-statement probe is reused unchanged; no auxiliary Lean source
is added. No production proof moves outside the measured main tree. Shared
modules count independently in each closure, so rows must not be added.
External Lake dependencies remain excluded. No minimality or build-speed claim
is made.

Chen's closure grows by +14 effective lines: the existing shared
error-envelope module gains 19 lines and its Pan quotient provider saves five.
The other changed providers, including the literal Jurkat–Richert module, are
not in the current Chen theorem import closure. Module names alone are not used
to infer closure membership. The complete main tree and Li–Liu closure still
save 187 lines. Separate concurrent `research/wu2008` sources and numerical
certificates are excluded. The changed `MathlibNt/Wu2004MeanValue` files belong
to the main library and are actual Li–Liu dependencies.

## Acceptance

All nine gates pass: warning-free 1,802-module full build (10,510 Lake jobs),
both public literal/axiom probes, unchanged internal-strengthening contracts,
five named-module kernel replays and script tests (115 passes, one optional
full-export fixture skip). Replays cover `Goldbach.Theorem`, `Goldbach.Checks`,
`Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks` and `Goldbach.All`
over rebuilt imports; separate replays of every imported module are not claimed.

All 1,808 main source/configuration/checker fingerprints and the separately pinned
statement probe match after every gate. The complete census preserves all
10,404 old public names/kinds/type hashes, with no missing or changed types.
Only the shared Pan maximum theorem is added. The existing budget name retains
its type and has verified upstream ownership. Private/generated names are excluded
from the public count. Seven private names disappear: five replacement statements
have matching old kind/type hashes; two unit-residue proofs are inlined into the
new shared maximum proof. No separate public residue alias or matching hash for
such an alias is claimed. The retained private squarefree statement keeps its
kind/type hash and actually reaches the generic Mathlib theorem.

All eight full-file prototypes passed warning-as-error compilation before
application. Three initial Pan maximum drafts lacked an explicit finite-image
index type and failed elaboration; only the three corrected files were recompiled,
with unchanged successful prototype hashes checked. No failing draft or forward
assumption is used in acceptance.

All six public endpoints preserve their exact constants and quantifier order:
`D19`, original prime conditions, `r^10 ≤ q^9`, the genuine real exponent,
Liu's singular series, strict `1/2500`, fixed `κ < 515093/800000000` before the
threshold and Chen's `0.67`. The three unconditional internal Euler positivity
statements are rechecked. Public axioms remain only `propext`, `Classical.choice`
and `Quot.sound`. Final producer reachability, all grids, precision and release
checks are unchanged.

The freshly extracted and locally rendered Blueprint has 68 nodes,
120 edges, four chapters and all six original exits, with matching source
positions, graph and annotations. This is an uncommitted local snapshot, not a
deployment. Historical source-size cohort statistics remain separate from current
totals; independent Wu research documentation is preserved.

See [validation](../research/liliu-low-budget-cleanup/validation.json),
[pinned inputs](../research/liliu-low-budget-cleanup/validation-inputs.json),
[type preservation](../research/liliu-low-budget-cleanup/type-preservation.json),
[eight-file changes](../research/liliu-low-budget-cleanup/changes.json),
[private sharing/inlining](../research/liliu-low-budget-cleanup/private-proof-redirects.json),
[retained squarefree statement](../research/liliu-low-budget-cleanup/retained-private-statement.json),
[moved budget and actual consumers](../research/liliu-low-budget-cleanup/moved-public-proofs.json),
[source sizes](../research/liliu-low-budget-cleanup/source-size.json) and
[Blueprint evidence](../research/liliu-low-budget-cleanup/blueprint-validation.json).

```sh
python3 research/liliu-low-budget-cleanup/reproduce.py --output /tmp/liliu-low-budget-recheck
python3 research/liliu-cleanup/measure_main.py
```

Use a new output directory. Default checks cover the main tree only;
`--include-wu` explicitly requests separate checks of a stable rebuilt Wu tree.
No saving from unimplemented follow-up candidates is counted here.
