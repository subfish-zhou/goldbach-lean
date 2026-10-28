# Chen 1+2: comparison with the five supplied original papers

This second audit follows the structural cleanup in
[CHEN_REDUNDANCY_AUDIT.md](CHEN_REDUNDANCY_AUDIT.md). It uses the five complete
PDFs supplied locally in `papers/`. Their fingerprints and reading locations
are recorded in [the paper manifest](../research/chen-paper-audit/papers-manifest.json).
The PDFs and OCR working text remain outside the tracked source package.
OCR is a search aid: the optimizer, numerical-margin and distribution formulas
used in the decisions below were checked against page images.

The comparison covers the inputs actually used by the Chen development, not
all applications and historical results in these papers. It does not claim a
recursive review of every item in their bibliographies.

## Reading locations and implementation decisions

| Original source | Reviewed locations | Consequence for this development |
|---|---|---|
| Chen, *On the representation of a larger even integer as the sum of a prime and the product of at most two primes*, Scientia Sinica 16(2) (1973), 157–176 | Theorem I, p. 158; Lemma 2; Lemmas 7–9 and the final argument, pp. 170–176 | Keep the actual representation count and the `0.67` target. The switched upper bound and distinct-medium-prime lower estimate are different obligations. |
| Pan Cheng-dong, Ding Xia-xi, Wang Yuan, *On the representation of every large even integer as a sum of a prime and an almost prime*, Scientia Sinica 18(5) (1975), 599–610 | Theorem 2, pp. 599–600; Corollary (2.30), p. 604; Sections III–IV, especially (4.5), p. 609 | Retain coprimality screens and divisor-weighted mean-value payment. The alternative lower-sieve calculation proves positivity with a `1/10` margin in its own notation; this is not a replacement certificate for the project's exact `0.67` bound. |
| Jurkat–Richert, *An improvement of Selberg's sieve method I*, Acta Arithmetica 11 (1965), 217–240 | Definition of `H_k(M)`, p. 218; delay functions, pp. 226–227; Theorem 5 and proof, pp. 230–232 | `H_k(M)` controls divisor counts against `y/d`. It does not identify the actual Goldbach density `1/(p-1)` with `1/p`. The implemented modern comparison remains necessary. |
| H.-E. Richert, *Selberg's sieve with weights*, Mathematika 16(1) (1969), 1–22 | Assumptions (A1)–(A3), pp. 3–7; Theorem A, p. 7; ordinary Bombieri (4.18) and its weighted use, pp. 18–20 | Richert allows general local densities, but quotes the general sieve theorem. A citation cannot replace a formal proof of that theorem. Preserve the distribution remainder and its divisor-weight payment; simplify its finite arithmetic instead. |
| Wang Yuan, *On the representation of large integer as a sum of a prime and an almost prime*, Scientia Sinica 11(8) (1962), 1033–1054 | Hypotheses (R), (R*), p. 1033; Theorem A and the explicit Selberg coefficients, pp. 1036–1037 | Isolate the finite optimizer from the conditional analytic estimate. The same finite algebra applies to a general bounding sieve and arbitrary cutoff, so three independently written optimization proofs can share one implementation. |

The Pan–Ding–Wang author order above follows the uploaded first page. Existing
Lean names containing `PanWangDing` remain compatibility identifiers. The
Jurkat–Richert PDF consists of two-page spreads: PDF page 1 right starts at
journal p. 217 and PDF page 13 left ends at p. 240. The facing pages 216 and 241
belong to adjacent material and are excluded. Wang's scan has an additional
outer page numbering; citations above use the journal pages, not that numbering.

## Source-to-code checkpoints

| Source obligation | Current implementation checkpoint | What the comparison rules out |
|---|---|---|
| Chen's final count and distinct-medium-prime lower estimate | [Public count](../Goldbach/Theorem.lean) and [actual Chen–Richert consumer](../MathlibNt/SieveTheory/LinearSieve/JurkatRichert/JurkatRichert1965ChenRichertConsumer.lean) | Replacing the quantitative count by bare positivity, or merging the distinct lower estimate with the switched upper estimate. |
| Jurkat–Richert Section 13 functions and the actual-density comparison | [Section 13 construction](../MathlibNt/SieveTheory/LinearSieve/JurkatRichert/JurkatRichert1965Section13HatSource.lean) and the Chen–Richert consumer above | Deleting the modern lower/upper comparisons on the assumption that the literal 1965 density model already supplies them. |
| Richert (4.18) and the weighted ordinary-prime remainder | [Unconditional modern producer](../MathlibNt/AnalyticNumberTheory/BombieriVinogradov/Bombieri1965Richert418Unconditional.lean) and [weighted consumer](../MathlibNt/SieveTheory/Distribution/Bombieri1965RichertWeightedConsumer.lean) | Treating the cited distribution theorem as an assumption, or discarding its weighted payment. |
| Pan–Ding–Wang Theorem 2 applied to the switched source | [Unconditional Liu–Pan producer](../MathlibNt/SieveTheory/Distribution/LiuPan/LiuPanUnweightedUnconditional.lean) and its coprime/principal correction inputs | Dropping coprimality restrictions, principal contributions or the actual discrepancy in favor of an unproved source proposition. |

These are application checkpoints, not claims that every intermediate proof is
a literal transcription of the corresponding paper. The retained distribution
and actual-density producers use the replacement arguments documented in their
own module headers.

## One finite optimizer, two specializations

For a `BoundingSieve` with squarefree product `P`, density `ν` and local Selberg
factor `g`, put

```text
C_R = {d : d divides P and d ≤ R}
G_R = ∑ e ∈ C_R, g(e)
x_R(e) = μ(e) g(e) / G_R  on C_R, and 0 otherwise
λ_R(d) = (1/ν(d)) ∑ e ∈ C_R, d|e, μ(e/d) x_R(e)  on C_R,
         and 0 otherwise.
```

For `R ≥ 1`, the single generic construction proves support, `λ_R(1)=1`,
reverse-divisor inversion, exact quadratic main term `1/G_R`, and
`|λ_R(d)| ≤ 1`. It uses only the `BoundingSieve` hypotheses. Wang's analytic
hypothesis (R*) is not an input to these finite identities.

The common implementation is
[TruncatedOptimalWeights.lean](../MathlibNt/SieveTheory/Selberg/TruncatedOptimalWeights.lean).
It also owns the shared restricted Möbius cancellation lemmas, preserving their
existing declaration names.

The [full-divisor optimizer](../AnalyticNumberTheory/Sieve/SelbergUpperBound.lean)
now specializes the theorem with `R=P`. A divisor of positive `P` is at most `P`,
so this cutoff retains the whole divisor lattice. The original full-divisor
coordinate formula can differ from the zero-extended truncated formula outside
that lattice. Its coordinate identification is therefore proved only on
`l|P`; its actual weight functions are proved equal everywhere.

The [Liu optimizer](../MathlibNt/SieveTheory/Selberg/Liu/LiuSelbergOptimalWeights.lean)
uses the actual source modulus and cutoff. For primes in that modulus,
`ν(p)=1/(p-1)` and `g(p)=1/(p-2)`. Equality of the finite denominators and of the
coordinate and weight functions turns its normalization, inversion, minimum
and absolute-value bounds into direct specializations. The public definitions
are retained, and their equalities with the generic construction are proved.
The analytic lower bound for `G_R` and the switched-source error estimate remain
separate obligations.

## Further finite arithmetic reductions

The [divisor-weight proof](../MathlibNt/SieveTheory/Selberg/SelbergUpperBound.lean)
now uses Mathlib's prime-factor union and disjointness identities for coprime
integers. This removes a separate proof of that disjointness and unnecessary
nonzero-denominator subcases. Both existing public divisor-weight definitions
remain available; their multiplicativity proofs share the same result.
The varying-prime sieve actually consumes the squarefree divisor-sum bound,
so that module is now imported explicitly there. Removing the bound from its
real consumer would be invalid; no saving is claimed for that dependency.

The [convolution proof](../MathlibNt/SieveTheory/Selberg/Liu/LiuSelbergDenominatorConvolution.lean)
uses `(f*g)/id = (f/id)*(g/id)` termwise on the divisor antidiagonal. The identity
`d*e=n` and ordinary division multiplication suffice. Separate zero cases,
nonzero divisor proofs and field cancellation are unnecessary.

## Measured scope

The [incremental change record](../research/chen-paper-audit/changes.json)
compares this phase with the previously accepted uncommitted cleanup snapshot,
including the new common module and all moved code. The consolidation
saves **598 effective code lines**, 593 physical lines and 26,574 UTF-8 bytes.
This is an additional saving, not a recount of the earlier 115,586-line cleanup.

| Source file | Effective lines before | Effective lines after |
|---|---:|---:|
| `Selberg/Liu/LiuSelbergOptimalWeights.lean` | 1,060 | 215 |
| `Selberg/SelbergUpperBound.lean` | 177 | 141 |
| `Selberg/Liu/LiuSelbergDenominatorConvolution.lean` | 445 | 431 |
| `Analytic/SelbergUpperBound.lean` | 299 | 93 |
| `Selberg/TruncatedOptimalWeights.lean` | 0 | 503 |
| `Selberg/Liu/LiuSelbergMainTermInstantiation.lean` | 25 | 24 |
| `Switching/VaryingPrimeSieve.lean` | 1,373 | 1,374 |

The new common module is included in the after total; extracting code alone
is not counted as a saving.

The [current whole-tree size report](../research/chen-paper-audit/source-size-after-fulltext.json)
uses the original `c4e1b8d0` baseline. The earlier audit and its validation records
remain historical snapshots. The [new validation record](../research/chen-paper-audit/validation.json)
accepts all 2,143 main source modules, both literal/axiom probes, five public-module
kernel replays, and 115 script tests with one optional full-export fixture skipped.
All 11,864 compared public declaration types from the preceding main snapshot
match. The [local Blueprint](../research/chen-paper-audit/blueprint-validation.json)
is freshly rendered and checked. Wu's unchanged sources and existing receipts
are revalidated; its full historical build is not repeated.

The [fresh dependency census](../research/chen-paper-audit/analysis-after-fulltext.json)
records the current compiled reference closure. A module with no reached
ordinary declaration is not automatically removable: elaboration can still
use its notation, instances or tactic registration. In particular, moving the
Möbius helpers puts the full-divisor optimizer outside Chen's stored-reference
closure; its documented generic finite-sieve API remains in the public library.
The census reports that distinction explicitly. These measurements do not claim
a mathematically minimal proof or a review of every recursive reference.
