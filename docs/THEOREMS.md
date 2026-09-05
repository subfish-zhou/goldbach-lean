# Theorems and interpretation

## Qualitative endpoint

`Goldbach.chen_theorem : Goldbach.ChenTheorem` has no analytic hypothesis
parameter. The threshold is chosen before the even integer. The second summand
must be a prime or a product of two primes, so neither zero nor one is admitted.
The factors of the composite summand need not be distinct.

The implementation theorem is
`MathlibNt.ChensTheorem.chens_theorem_unconditional`. It uses
`MathlibNt.ChensTheorem.Semiprime`, whose meaning here is **at most two prime
factors, counted with multiplicity, and value at least two**. This historical
internal name differs from Mathlib's `Nat.IsSemiprime`, which means exactly two
prime factors. The public statement avoids this terminology altogether.
`MathlibNt.ChensTheorem.semiprime_iff` proves the exact conversion used by the
public theorem; `Goldbach/Checks.lean` checks the expanded target directly.

## Quantitative endpoint

`Goldbach.representation_lower_bound` proves that, eventually for natural `N`,
if `N` is even, then

```text
0.67 * liuSingularSeries(N) * N / log(N)^2
  <= card(chenGoodRepresentations(N)).
```

The count is a finite set of prime first summands whose complements are at
least two and have at most two prime factors. It is not an abstract surrogate
count, and it does not count ordered factorizations of the second summand.
The precise finite-set and singular-series definitions remain in
`MathlibNt.SieveTheory.SwitchingPrinciple` and
`MathlibNt.SieveTheory.SingularSeries`, respectively (declaration namespaces).
In particular, changing singular-series normalization would change the displayed
coefficient; the theorem is stated using the literal `liuSingularSeries`:

```text
product_{prime p > 2, p divides N} (p - 1)/(p - 2)
  * product_{prime p > 2} (1 - 1/(p - 1)^2).
```

The infinite product is convergent and positive. The prime `2` is omitted;
there is no additional leading factor `2` in this normalization.

The underlying implementation theorem is
`MathlibNt.ChensTheorem.chen_good_representations_lower_bound_unconditional`.

## Scope

- This release proves an existential sufficiently-large threshold, not a
  verified explicit cutoff or a check of every smaller even integer.
- A prime plus a product of two primes is permitted; this does not prove the
  binary Goldbach conjecture.
- The stronger 1+1.9 target is not part of this version's public contract.
- Conditional intermediate theorems are ordinary reusable lemmas. They are not
  advertised as unconditional producers; the final endpoint supplies their inputs.
