# Theorems and interpretation

The Goldbach research program has formalized Chen's **1 + 2 theorem** and its
quantitative representation bound. Work on **1 + 1.9** is in progress; stronger
results remain further research directions. The public declarations below
state the completed results.

## Qualitative endpoint

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

## Quantitative endpoint

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

Both results are sufficiently-large statements with existential thresholds.

Conditional intermediate theorems expose reusable analytic inputs. The final
implementation endpoints supply those inputs with proved results. The public
theorems are checked under Lean's standard logical axioms using the rules in
[VERIFICATION.md](VERIFICATION.md).
