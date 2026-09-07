# Theorems and interpretation

The Goldbach research program has formalized Chen's **1+2 theorem** and
Li–Liu's **1+1.9 theorem**, with quantitative bounds for both. Stronger results
remain a research direction. Import `Goldbach` for Chen,
`Goldbach.OnePlusOneNine` for Li–Liu, or `Goldbach.All` for both.

## Li–Liu 1+1.9: literal representation

`Goldbach.one_plus_one_nine` proves:

```lean
∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
  p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
    N = p + r * q ∧ r ^ 10 ≤ q ^ 9
```

The size condition is exact natural-number arithmetic. The equivalent
`Goldbach.one_plus_one_nine_real` uses `(r : ℝ) ≤ (q : ℝ)^((19/10 : ℝ) - 1)`.
Taking `r = 1` includes a sum of two primes; taking `r` prime gives the constrained
product of two primes. This refines the 1+2 representation by controlling the
relative sizes of its factors. The original Chen interface and proof route
remain separately importable.

The implementation endpoints are `goldbach_onePlusOneNine_nat_unconditional`
and `goldbach_onePlusOneNine_unconditional` in
`MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig`, supplied by
[LiLiuGoldbachOneNineUnconditional.lean](../MathlibNt/SieveTheory/LiLiuGoldbachOneNineUnconditional.lean).

## Li–Liu 1+1.9: distinct-prime count

In namespace `MathlibNt.SieveTheory.LiLiuOnePlusOneNine`, `D19 N` is the
cardinality of the finite set of primes `p ≤ N` for which there exist `r, q`
with the representation and size condition above. Each eligible `p` contributes
once, regardless of the number of witness pairs `(r, q)`. The definition is in
[LiLiuGoldbachOnePlusOneNineFinite.lean](../MathlibNt/SieveTheory/LiLiuGoldbachOnePlusOneNineFinite.lean).

`Goldbach.one_plus_one_nine_count` proves that there is a natural threshold
`K ≥ 4` such that every even `N ≥ K` satisfies the strict inequality

```text
(1/2500) * (liuSingularSeries(N) * N / log(N)^2) < D19(N).
```

Here `1/2500 = 0.0004` exactly. The singular series is the same Liu normalization
displayed below for Chen's quantitative theorem, and `log` is the natural
logarithm. The count is cast to the real numbers in the inequality.

`Goldbach.one_plus_one_nine_lower_bound` gives the stronger family: for every
fixed real `κ < 515093/800000000`, there exists a natural threshold `K ≥ 4`
such that, for all even `N ≥ K`,

```text
κ * (liuSingularSeries(N) * N / log(N)^2) <= D19(N).
```

The coefficient is chosen before the threshold, which may depend on it. The
strict upper limit on `κ` is part of the theorem's hypothesis. These endpoints
use `goldbach_D19_gt_paper_0004` and
`goldbach_D19_author_lower_of_coefficient_lt` in the `GoldbachBig` namespace,
proved in [LiLiuGoldbachG11AuthorQuantitative.lean](../MathlibNt/SieveTheory/LiLiuGoldbachG11AuthorQuantitative.lean).

## Chen 1+2: qualitative endpoint

`Goldbach.chen_theorem : Goldbach.ChenTheorem` proves:

```text
exists N₀ : ℕ, for every N : ℕ,
  N₀ <= N -> Even N ->
    exists p q : ℕ,
      p is prime and
      (q is prime or q is a product of two primes) and
      N = p + q.
```

One threshold `N₀` works for all subsequent even integers. The representation
may depend on `N`: first choose the threshold, then take any even `N` above it,
then obtain `p` and `q`. The theorem establishes the existence of this threshold.
Both summands are at least two. In the composite case the two prime factors
may coincide.

The implementation theorem is
`MathlibNt.ChensTheorem.chens_theorem_unconditional`. Its analytic inputs are
supplied by proved theorems, so the public result is unconditional. It uses
`MathlibNt.ChensTheorem.Semiprime`, meaning **at most two prime factors, counted
with multiplicity, and value at least two**. Mathlib's `Nat.IsSemiprime` means
exactly two prime factors. The public statement spells out the alternatives
using primality and multiplication.
`MathlibNt.ChensTheorem.semiprime_iff` proves the conversion used by the public
theorem; `Goldbach/Checks.lean` checks the expanded target directly.

## Chen 1+2: quantitative endpoint

`Goldbach.representation_lower_bound` proves that, eventually for natural `N`,
if `N` is even, then

```text
0.67 * liuSingularSeries(N) * N / log(N)^2
  <= card(chenGoodRepresentations(N)).
```

Here `log` is the natural logarithm, and the inequality is over the real numbers.
The eventual quantifier gives a threshold beyond which the inequality holds for
every even `N`.

`chenGoodRepresentations(N)` is the finite set of **prime first summands** `p`
whose complements `N - p` are at least two and have at most two prime factors,
counted with multiplicity. Each eligible `p` contributes one to the cardinality;
factoring its complement in different orders leaves that contribution unchanged.
The finite-set definition is in the declaration namespace
`MathlibNt.SieveTheory.SwitchingPrinciple`.

The coefficient `0.67` uses the exact normalization of `liuSingularSeries` in
`MathlibNt.SieveTheory.SingularSeries`:

```text
liuSingularSeries(N) =
  product_{prime p > 2, p divides N} (p - 1)/(p - 2)
    * product_{prime p > 2} (1 - 1/(p - 1)^2).
```

The second product is infinite, convergent and positive. Both products run over
odd primes, and their product is the complete normalization used in the bound.
The constant `0.67` belongs to this normalization.

The implementation theorem is
`MathlibNt.ChensTheorem.chen_good_representations_lower_bound_unconditional`.
`Goldbach/Checks.lean` checks both the public theorem and this implementation
endpoint against the same explicit quantitative type.

## Thresholds and proof inputs

All public results are sufficiently-large statements with existential thresholds.

Conditional intermediate theorems expose reusable analytic inputs. The final
implementation endpoints supply those inputs with proved results. The public
theorems are checked under Lean's standard logical axioms using the rules in
[VERIFICATION.md](VERIFICATION.md).
