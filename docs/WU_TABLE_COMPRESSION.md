# Wu cumulative recurrences and exact certificate compression

2026-10-26. Following [Hf4 compression](WU_HF4_COMPRESSION.md), this phase retains
the final 1+1.8938 result, mathematical grids, rounding scales and every original
numerical bound. It removes intermediate certificates derivable from recurrences
or exact arithmetic.

## Changes in this phase

**Fourth term: reconstruct cumulative integral tables by recurrence.** `B` and
`outer` each have 10,541 original values. These values accumulate upward-rounded
trapezoidal integrals and error terms, rather than providing independent inputs.
This phase stores every fourth original value as an anchor and recovers the
others in at most three steps:

\[
A_{i+1}=A_i+\left\lceil
\frac{3\cdot4000^2(q_i+q_{i+1})+E\cdot10^{15}}
{6\cdot4000^3}\right\rceil,
\qquad E=2\text{ or }56.
\]

This is an exact integer recurrence, with no new integral approximation. All
**21,082 values** in the two tables match the fixed Git baseline individually;
out-of-range indices still return zero. Anchor spacing controls storage and
kernel reduction length, leaving the mathematical grid and precision unchanged.

A shared ceiling-payment lemma supplies the same mathematical proof for the
internal steps of 84 payment blocks; finite checks occur only at anchor joins.
Original `BPay`/`OuterPay` block statements remain unchanged, as do `Bq`,
`outerq` and the C/D tables.

**Sixth continuous gain: remove unnecessary intermediate rounding.** Previously,
the rounded density and profile were certified separately before certifying
their product. This phase certifies the original payment directly with the same
exact rational expression and original analytic panel lemma. It deletes 32
Panels files while retaining all 32 public GridBlock conclusions. Original
payments, tail tables, the 1024-cell grid, final certificate and lower bound
are unchanged.

**Seventh and ninth terms: shared exact logarithm checks.** Rational evaluation
of the same twelve-term logarithm envelope uses one proof of conversion to the
original real formula, followed by finite blocks checked with `decide +kernel`.
The original integer payments, sums and final upper bounds at 256 seventh-term
points and 512 ninth-term points are unchanged. The phase deletes 48 pointwise
proof files.

These changes preserve the mathematical interfaces consumed downstream.
Deleted internal pointwise lemmas and old data-block declarations are not
retained for compatibility.

## Actual reductions

Measurements cover local Lean sources, excluding external Lake dependencies,
Python generators, documentation and audit material. Every new shared lemma is
included.

| Component | Net effective lines removed |
|---|---:|
| Fourth-term cumulative recurrences and payment proofs | 15,376 |
| Sixth continuous gain | 9,231 |
| Ninth term | 4,705 |
| Seventh term | 2,343 |
| **Total** | **31,655** |

Complete Wu tree: **677,670 → 646,015** effective lines.

Final theorem import closure: **636,916 → 605,261** effective lines, a **4.97%**
reduction in this phase. It also removes **33,295** physical lines and
**1,638,393** source bytes. There are 80 deleted modules and 19 new modules;
the complete tree has **4,713** modules and the final closure **4,326**.

The cumulative saving from the original 1,126,636-line closure is **521,375**
lines. These are complete imported-module measurements, rather than minimal
declaration-level proof sizes.

## Validation and evidence

The audit records a comparison of 120 retained theorem statements, identical
apart from whitespace; hashes of 4,574 unchanged source files; preservation of
the original seventh/ninth data and sum text; and an independent exact integer
comparison of both cumulative tables.

See [wu-table-audit](../research/wu-table-audit/README.md) for the full build,
literal propositions, axioms, independent kernel replays and generator records.
Earlier phase reports and acceptance records remain historical snapshots.

```sh
python3 research/wu2008/build.py --all --jobs 2 --lean-threads 2
python3 research/wu2008/check_classical.py
python3 research/wu2008/verify_sources.py
python3 research/wu-table-audit/measure.py
python3 research/wu-table-audit/check_values.py
```

The last command reads the original tables from fixed commit
`c4e1b8d00dda9661140f95e0f03f0d5a08d636c2`, verifies their original source hashes,
and reconstructs values from the actual anchors in the current sources. It
requires that Git history object. This comparison is not a Lean proof; source
builds and kernel checks independently verify the original numerical bounds.
