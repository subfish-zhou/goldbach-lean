# Derivative automation and proof-maintenance boundaries

## Shared tools

- [`MathlibNt.Tactic.PolynomialDeriv`](../MathlibNt/Tactic/PolynomialDeriv.lean)
  provides `polynomial_deriv`. It represents a univariate real polynomial as a
  `Polynomial`, applies Mathlib's `Polynomial.hasDerivAt`, and reduces the
  remaining expression equalities. Applications retain their original functions,
  derivative formulas, coefficients and hypotheses.
- [`MathlibNt.Tactic.ElementaryDeriv`](../MathlibNt/Tactic/ElementaryDeriv.lean)
  provides `elementary_deriv [facts]`. It builds ordinary derivative proofs for
  sums, differences, products, negation, division, reciprocals, natural powers
  independent of the differentiation variable, `Real.log`, and `Real.exp`.
  Supplied `HasDerivAt` proofs are reused at their stated evaluation point.

Neither tactic is a new mathematical axiom. Their outputs are checked by Lean's
kernel. They do not claim a general decision procedure for arbitrary elementary
functions, variable exponents, square roots, or trigonometric differentiation.
An unsupported subexpression can be handled by supplying its derivative proof.

Variable denominators and logarithm arguments produce nonzero proof obligations.
The elementary tactic tries the current hypotheses and ordinary tactics; an
unproved obligation remains a goal. For real logarithms the condition is
nonzero, not necessarily positive. Division by a constant uses the appropriate
constant-division derivative theorem, including Lean's totalized zero division.

For example, this complete proof is also covered by the regression tests:

```lean
import MathlibNt.Tactic.ElementaryDeriv

example (x : ℝ) (hx : x ≠ 0) : HasDerivAt Real.log (1 / x) x := by
  elementary_deriv []
```

## Concrete uses

Polynomial certificates in S3, S4, S5, B10, G9, G12 and the positive scalar
polynomial reuse `polynomial_deriv`. The G9 and G12 logarithmic primitives reuse
`elementary_deriv`, retaining their partial-fraction identities and denominator
conditions. The Liu majorant primitive and normalized alternating-pair primitive
use the same elementary tool. The G67 primitive family uses a separate short
proof construction already expressed with existing Mathlib machinery.

The point is to keep the mathematical formula and the final algebra visible,
without repeating every multiplication and addition rule. None of these source
rewrites changes an integration range, endpoint convention, arithmetic weight,
sieve constant or public number-theoretic conclusion.

## Regression checks

These modules are included in the normal `MathlibNt` build:

```bash
lake build MathlibNt.Tactic.Tests.PolynomialDerivTests
lake build MathlibNt.Tactic.Tests.ElementaryDerivTests
lake build MathlibNt.Tactic.Tests.DerivativeObligationTests
```

They cover valid polynomial and logarithmic derivatives, an exponential quotient,
constant denominators, reuse of a supplied derivative, rejection of wrong
formulas and missing hypotheses, and inspection of an actual residual `x ≠ 0`
goal. A failed attempt to finish a proof is distinguished from a differentiation
procedure that fails before producing its obligations.

## Local timing observations

Source reduction is not automatically a compilation-speed improvement. Earlier
polynomial batches shortened the code while their sampled module builds became
slightly slower. Profiling the Liu majorant example instead found substantial
work in a following `norm_num` call, rather than in proof-to-syntax conversion.
Replacing that call by `simp only` retains the original generated equation lemma
and lets the subsequent `field_simp` and `ring` finish the algebra.

For that isolated candidate, three repeated profiles gave a median sum of timed
proof stages of 1.305 seconds with default `norm_num`, 1.022 seconds with
`norm_num only`, and 0.801 seconds with `simp only`. Some later algebra stages
became slower, but less than the saved preliminary normalization work.

A separate uninstrumented comparison rotated the order of the original manual
proof, the default-normalization short proof and the selected short proof. Their
three-run median full-module times were 7.483, 7.334 and 7.084 seconds respectively.
The first independent selected-candidate compile was 8.034 seconds, illustrating
why an individual observation is insufficient. These measurements used the pinned
Lean toolchain, two threads and frozen dependencies before the helper imports were
moved into the library namespace. They are not measurements of a clean full
release, of GitHub Actions, or a general speedup guarantee for either tactic.

## Generated-name compatibility

The intended mathematical theorem statements and definition values are preserved;
not every compiler-generated auxiliary name is retained. In particular, the
Case-II transport and the normalized alternating-pair derivative retire generated
simplifier helpers. Source refactoring can also change binder names inside an
auxiliary proof without changing its mathematical meaning.

The alternating-pair change retires seven `_simp_1_*` theorems. Their bound
runtime constant-expression consumers and current import registrations were
checked separately from compilation and kernel validity. This is a bounded
compatibility check, not a promise that arbitrary reflection or an old direct
`#check` of a retired name still works. Downstream code should refer to the named
mathematical theorem rather than such generated helpers. Whole-project builds,
public-statement checks and kernel replay remain separate integration gates.
