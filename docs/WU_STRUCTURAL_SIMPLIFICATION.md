> This page is the previous phase's snapshot. Hf4 subsequently connects an
> exactly equivalent kernel to the main proof; see the
> [implementation and acceptance](WU_HF4_COMPRESSION.md).

# Wu 1+1.8938: structural simplification experiments

2026-10-26. This phase keeps parameters and numerical precision unchanged while
examining analytic envelopes, the nine-node weighted comparison, and the
mathematical structure of the fifth and sixth gain integrals.

## Integrated: a direct analytic inequality for the fifth gain

Previously, `log_ratio_lower` proved a degree-seven logarithm polynomial lower
bound, then discarded its cubic, quintic and septic terms. It now applies
Mathlib's inequality directly:

\[
\frac{2u}{u+2}\le\log(1+u)\quad(u\ge0).
\]

Substituting \(u=(y-x)/x\) gives the same conclusion
\(2(y-x)/(y+x)\le\log(y/x)\), with the original assumptions \(0<x\le y\).
All numerical tables, public mathematical statements, the fifth-gain lower
bound and the final 1.8938 result remain unchanged.

The change affects `WSrcFifthGainAnalyticEnvelope.lean` and removes two obsolete
diagnostic print commands from its diagnostic root.

| Scope | Effective lines before | Effective lines after | Saving |
|---|---:|---:|---:|
| Complete Wu tree (4,771 modules) | 728,674 | 728,665 | 9 |
| Final theorem import closure | 688,336 | 687,911 | 425 |

Closure module count drops from 4,389 to 4,384, with 494 fewer physical lines.
The five WE09 modules leaving the closure still support other research branches
and remain in the source tree. Their removal from this closure is a dependency
reduction, rather than a whole-tree deletion. Standalone experiments and audit
materials are outside the main proof tree and excluded from these savings.

## Verified but not integrated in this snapshot: a common Hf4 polynomial envelope

Set \(x=(1+z)/(1-z)\), and fix

\[
P(z)=2z(1+z^2/3+z^4/5+z^6/7),\qquad
U(z)=P(z)+\frac{2z^9}{9(1-z^2)}.
\]

The [standalone Lean experiment](../research/wu-structural-audit/hf4/Hf4SeriesEnvelope.lean)
proves four results:

- For \(0\le z<1\), \(P(z)\le\log x\le U(z)\), using the existing analytic
  logarithm bounds.
- For \(0\le z\le1/3\), the old `low(x)` is at most \(P(z)\).
- For \(0\le z<1\), \(U(z)\) is at most the old `up(x)`.
- For \(0\le z\le1/4\), \(U(z)\) is even at most the old split `su(x)`.

The last result allows removal of the two-factor split in the upper envelope
for `zeroRatio=(t+2)/3`, \(1\le t\le3\). Other lower envelopes could be replaced
factor by factor, but their split cannot simply be removed: at the actual
argument \(x=5/4\), the exact difference is

\[
P((x-1)/(x+1))-sl(x)
=-\frac{7804301671255727}{13925693418881136407739000}<0.
\]

These are strict analytic results, without sampling or changing expansion
orders. All four experiment theorems pass Lean with only the standard classical
axioms. In this snapshot they are not connected to the existing 418-node DAG
and 40 integration panels. Overall kernel intervals, coefficient signs and
replacement integral certificates have not yet been verified, so these
experiments yield no main-tree source reduction. The next substantive step is
a shorter kernel and rebuilt panel certificates. SymPy operation counts are
exploratory evidence, rather than measurements of actual code savings.

## Routes not adopted in this phase

The existing nine-node proof already uses a short finite subsolution comparison.
The canonical dual vector has full support for the current strictly positive
matrix. Turning the existing coordinatewise comparison into a weighted quantity
does not itself remove rows or columns. Pointwise table extensions and continuous
integral monotonicity would still be needed. Adding a dual lemma alone gives no
net saving; a different sparse certificate or direct weighted integral proof
remains possible. See the
[exact matrix and dependency analysis](../research/wu-structural-audit/weighted-analysis.md).

Replacing `max` in the sixth gain by `lowerH` alone removes only three modules
from the closure and changes the public intermediate quantity `SourceSixth.amount`.
That route is not adopted.

The fifth gain already has an analytic reduction to thirteen weights, while
a substitution and Fubini remove one integration dimension from the sixth gain.
This phase finds no shorter further interchange proof preserving the existing
bounds, and adds no unused abstractions for these routes.

## Validation and reproduction

All 4,771 modules pass the full build, provenance and dependency receipts, both
1.8938/1.894 literal propositions, and standard-axiom checks. The changed analytic
envelope and final theorem modules also pass independent kernel replay over
imports verified by the full build. An independent replay of every module is
not claimed.

Evidence is in [wu-structural-audit](../research/wu-structural-audit/README.md).
The two earlier compression records remain historical snapshots. This phase
changes only two source files; the other 4,769 are byte-identical.
