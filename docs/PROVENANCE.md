# Source provenance and licensing

## Reader route and fixed mathematical source

Start with the [author report](https://subfish-zhou.github.io/goldbach-lean/report/)
for the public statements, two proof exits, and the paper-to-Lean correspondence
ledger. Continue with the [selected Blueprint](https://subfish-zhou.github.io/goldbach-lean/blueprint/)
for the finite weights and analytic arguments; use the
[structure browser](https://subfish-zhou.github.io/goldbach-lean/structure/) for
the full project-module and declaration-reference views and the
[Lean API](https://subfish-zhou.github.io/goldbach-lean/docs/) for exact statements.
These are progressively deeper reading layers.

The Li–Liu mathematical source is **Jiamin Li and Jianya Liu,
*Theorem $(1+1.9)$ on the Goldbach Conjecture*, arXiv:2606.05224**.
The comparison ledger fixes the public [v1 HTML](https://arxiv.org/html/2606.05224v1),
with [bibliographic record](https://arxiv.org/abs/2606.05224).
Theorem 1.1 is the unconditional Goldbach result; equation (4.4) specifies its
count by distinct primes `p`, and (1.3) specifies `C(N)`, the implementation's
`liuSingularSeries N`, without an additional factor two.

The paper contributes the asymmetric representation target, weighted-sieve
construction and analytic organization. The Lean development makes the finite
carriers, exception payments, uniformity and coefficient certificates explicit.
Its actual twelve-term route uses a separately defined factor-excluded
`goldbachG10Corrected` and a proved corrected finite inequality. The original
paper's tenth fibre and this implemented fibre remain separately named; the
correspondence ledger identifies the exact change of excluded modulus.

The natural-power and real-exponent public existence theorems use the earlier
positive-margin route. The strict `1/2500` count and the family of fixed
coefficients `κ < 515093/800000000` use the author-G11 count ledger. The stronger
coefficient family is a retained formal certificate, separately recorded from
the paper's strict `0.0004` conclusion. The paper's twin-prime Theorem 1.2 and
its Theorems 1.3–1.4 under `WEH(0.999)` have separate targets from these four
unconditional Goldbach interfaces.

## Original project sources

The Chen (1+2) implementation and the shared foundations reused by the
Li–Liu (1+1.9) development build on
[UyNewNas/chen-theorem-lean](https://github.com/UyNewNas/chen-theorem-lean), with
substantial subsequent proof completion and engineering changes. The reusable
analytics sources originate in
[UyNewNas/analytic-number-theory-lean](https://github.com/UyNewNas/analytic-number-theory-lean)
and subsequent local development. This package brings together the required
local source closure and the changes that complete the released proof.

The source package is distributed under the existing Apache-2.0 license.
Existing copyright and author notices in upstream source files are retained.

## Adapted prime-number-theorem proof

The `PrimeNumberTheoremAnd/` sources are an adapted minimal import closure from
[AlexKontorovich/PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
release `v4.32.2`, commit
`6a380f0c4658c04a420a9eb00b1ed62a1e3fde01`, under Apache-2.0.

The port uses Lean `v4.33.0-rc1` and the Mathlib revision pinned in this package.
Its documented adaptations make measurability, unit-circle norm, and
almost-everywhere arguments explicit in `Fourier.lean` and `Wiener.lean`, and
remove an obsolete redundant proof step in `MediumPNT.lean`. The import
extraction also omits three unused alternate decay lemmas that contained
unproved terms. The retained implementation carries the upstream proof into
this toolchain and is built and checked with the rest of the package.

## External Lean dependencies

`lake-manifest.json` records the exact Git revisions of Mathlib, LeanArchitect,
and their transitive dependencies. Lake fetches these packages separately from
the release archive, which excludes their source trees and cached artifacts.
Their own licenses and attribution remain applicable.

## Mathematical sources

The implementation assembles the completed Chen and Li–Liu theorems from the following
mathematical sources. Module documentation identifies the source variants and
adaptations used at each step.

- J. R. Chen, *On the representation of a large even integer as the sum of a
  prime and the product of at most two primes*, Scientia Sinica 16 (1973), 157–176.
- Jiamin Li and Jianya Liu (2026), the fixed public source above, its `1+1.9` result and distinct-prime count
  `D_{1,19/10}(N)`. The [finite representation module](../MathlibNt/SieveTheory/LiLiuGoldbachOnePlusOneNineFinite.lean)
  identifies the source labels `p+rq/r<`, `D1a` and `Goldbachbasic`; the
  [quantitative endpoint](../MathlibNt/SieveTheory/LiLiuGoldbachG11AuthorQuantitative.lean)
  combines the original counts with the certified integral estimates.
- The Jurkat–Richert linear-sieve and Richert weighted-sieve arguments, with
  precise source variants identified in the implementation module documentation.
- Suzuki's modern linear-sieve comparison results, which supply comparisons for
  the actual lower and upper source families. The modern upper comparison is
  attributed to Suzuki; the Jurkat–Richert modules document the 1965 input.
- Bombieri–Vinogradov, Pan-type convolution estimates, and Fouvry well-factorable
  distribution, with the separate implemented contracts below.
- Z. Liu, the Chen-theorem exposition and Selberg-sieve calculations associated
  with [arXiv:2203.07871](https://arxiv.org/abs/2203.07871).

Source references record the mathematical provenance of the Lean proofs.
The [verification guide](VERIFICATION.md) describes axiom inspection for both
public interfaces and the scope of their separate acceptance probes.

## Three distribution inputs and their implemented roles

### 1. Ordinary prime progressions

`standardBombieriVinogradov` in
[`Bombieri1965Richert418Unconditional.lean`](../MathlibNt/AnalyticNumberTheory/BombieriVinogradov/Bombieri1965Richert418Unconditional.lean)
supplies the maximal prime-progression error at a square-root/logarithmic
modulus cutoff. Its proof assembles the principal estimate, a proved
small-conductor Siegel–Walfisz input and large-conductor Vaughan/large-sieve
estimates. This is a modern replacement proof of the needed distribution
contract. The prime-prefix normalization is
`L_*(x) = 2/log 2 + integral_2^x dt/log t` for `x > 1`, with the specified
totalized endpoint convention for `x = 0,1`. The original-source `S1` remainder
is an actual consumer; the Blueprint explains the further weighted payment
needed when a conditioned modulus is a product.

### 2. Varying bounded coefficient–prime convolutions

[`LiLiuPanBoundedAggregate.lean`](../MathlibNt/SieveTheory/LiLiuPanBoundedAggregate.lean)
proves `liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving`.
For each requested logarithmic saving it chooses its constants, modulus
exponent and threshold **before** the natural scale, interval `(A1,A2]` and
real coefficient `f` vary, subject to `|f| ≤ 1`, `A2 ≤ N^(2/3)` and
`(log N)^(2B) ≤ A1`. The convolution sum stays inside the absolute value.
Low/high primitive-conductor estimates, the reciprocal-totient cofactor sum,
and the paid principal term produce this aggregate.

The actual consumers include
[`LiLiuGoldbachS2SwitchedDistribution.lean`](../MathlibNt/SieveTheory/LiLiuGoldbachS2SwitchedDistribution.lean)
and [`LiLiuGoldbachB10PanTwoEndpoints.lean`](../MathlibNt/SieveTheory/LiLiuGoldbachB10PanTwoEndpoints.lean).
The B10 window is treated by two prefix endpoints with their own geometry and
coprimality corrections. The fixed Chen coefficient has its separate
[`LiuPanUnweightedUnconditional.lean`](../MathlibNt/SieveTheory/Distribution/LiuPan/LiuPanUnweightedUnconditional.lean)
producer; the varying Li–Liu theorem reuses analytic ingredients at the broader
quantifier order. These implemented contracts are the precise counterparts
needed from the paper's weighted-distribution discussion and Lemma 3.1.

### 3. Signed well-factorable bilinear distribution

The fixed paper's Lemma 3.5 supplies the level `X^(5(1−ν)/9−ε)` for its
small-prime regime and a residue allowed to vary up to the scale. The proved
[`primeC2_goldbach_rectangle_kscale`](../MathlibNt/AnalyticNumberTheory/LargeSieve/LiLiuFouvryKGoldbachRectangle.lean)
uses the literal Goldbach residue and a prime coefficient filtered by
coprimality with `N`. For fixed divisor orders, logarithmic saving, scale factor
and positive gap, its threshold precedes the rectangle and coefficients.
Its contract has `4MT = x`, `T = x^ν`, `ζ ≤ ν ≤ 1/10+ζ/10`,
`0 < N ≤ Cscale*x`, a divisor-bounded long coefficient, and a signed
well-factorable modulus coefficient at `x^((5−5ν)/9−ζ)`.
The discrepancy is signed in the modulus before taking its absolute value.

[`G12FlexibleRectangle.rectangle_C2_bound`](../MathlibNt/SieveTheory/LiLiuGoldbachG12FlexibleRectangleC2.lean)
directly consumes this theorem. Curved boundaries and exceptional atoms are
paid in the counting layers. The separate low-G9 producer enters the exact
low/high partition in
[`LiLiuGoldbachS5PaperSplitUpper.lean`](../MathlibNt/SieveTheory/LiLiuGoldbachS5PaperSplitUpper.lean);
the extra low kernel factor `1/(1−u)` is retained. The author-G11 route derives
its mixed-level weight before the integral is estimated. These source-specific
applications and the rectangle contract are recorded separately from the
paper's more general distribution statements.

## Statement fidelity and proof foundations

The report's correspondence categories distinguish literal counts, proved
notation equivalences, replacement intermediate arguments and comparisons
still awaiting a line-by-line source review. A modern replacement proof retains
its mathematical attribution while identifying the implemented contract.

The four public Li–Liu theorem types carry no BV, Pan, Fouvry, integral-bound,
positivity or Elliott–Halberstam premise. The standard Lean logical principles
`propext`, `Classical.choice` and `Quot.sound` are distinct from an unproved
mathematical distribution hypothesis. The [verification guide](VERIFICATION.md)
specifies the checks for theorem types, transitive axiom reports and replay;
source correspondence and those execution checks are separate evidence layers.
