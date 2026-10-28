> This is the historical Hf4 snapshot; see the [subsequent cumulative-table and certificate compression](WU_TABLE_COMPRESSION.md) for current measurements and acceptance.

# Hf4 equivalent kernel and certificate compression

2026-10-26. Following the [structural experiments](WU_STRUCTURAL_SIMPLIFICATION.md),
this phase connects a shorter analytic expression to every integration panel.
The final target remains 1+1.8938, with unchanged parameters, precision and
original numerical bounds.

## Mathematical change: an equivalent kernel retaining the remainder

The previous degree-seven polynomial envelope gives only one-sided domination,
so it cannot directly replace the two-sided certificates for the original
`endpointCellMass`. This phase retains the exact rational remainder and sets

\[
z=\frac{x-1}{x+1}.
\]

After combination, the old lower and upper envelopes are exactly

\[
low(x)=\frac{2z(525+1050z+385z^2-280z^3-140z^4+12z^6-2z^7)}
 {105(1+z)^2(5-3z^2)},
\]
\[
up(x)=\frac{2z(105+105z-70z^2-70z^3-14z^4-14z^5-6z^6)}
 {105(1-z)(1+z)^2}.
\]

The source evaluates the polynomials in Horner form. Coordinates from the
original two-factor split simplify directly to \((x-1)/(x+3)\) and
\((x-1)/(3x+1)\), eliminating nested fractions.

`Hf4Quad.compactKernel_eq` proves equality of the new and old kernels on the
original integration interval \([1,3]\). `endpoint_compact_model` connects the
new kernel model to the original two-sided integral bounds. The definitions of
`kernel`, `paidWeight`, `endpointCellMass`, aggregate Q and the final theorem
remain unchanged.

## Certificate changes

- The arithmetic graph shrinks from **418** nodes to **381**.
- The same **40** panels, half-width \(1/40\), coefficients rounded downward
  and errors upward to \(10^{-14}\), and radical enclosures are retained.
- A rational `Certificate` stores each cubic model and error. A shared
  soundness lemma transfers rational side conditions to the original real
  `Model`; finite conditions are checked with `decide +kernel`.
- Every new interval is contained in its original interval; widths are about
  **63.38%–80.99%** of the originals. The 40 public `mass_bounds` statements
  are unchanged apart from whitespace. Downstream aggregate modules and final
  theorem source files remain byte-identical.
- The unreferenced old DAG is deleted, fourteen panel/batch files are replaced
  and four shared modules are added. Internal generated declarations such as
  the old `p` and `e` are replaced by certificate data; their old interfaces
  are not claimed to be preserved.

## Actual source size

These local Lean source measurements include every new shared lemma. They
exclude external Lake dependencies, Python generators, documentation and audits.

| Scope | Effective lines before | Effective lines after | Net saving |
|---|---:|---:|---:|
| Complete Wu source tree | 728,665 | 677,670 | **50,995** |
| Final theorem import closure | 687,911 | 636,916 | **50,995** |

The phase also removes **52,467** physical lines and **1,497,587** source bytes.
The full tree contains 4,774 modules and the final closure 4,387. Module count
rises by three, while shared lemmas replace substantial repeated proofs. The
closure shrinks by about **7.41%** in this phase, a cumulative saving of
**489,720** lines from the original 1,126,636.

The reduction includes fewer kernel operations and shared rational checks
replacing repeated real-arithmetic proofs. All numerical data and kernel
proofs remain; the measurement is not merely a change in line wrapping.

## Reproduction and validation

The self-contained generator uses only exact `Fraction` arithmetic from the
Python standard library. It reads neither old generated files nor temporary
directories. The generator is outside the trusted computing base: Lean checks
its output.

```sh
python3 research/wu2008/diagnostics/hf4_compact_certificates.py --output-dir research/wu2008/src --check
python3 research/wu2008/build.py --all --jobs 3 --lean-threads 2
python3 research/wu2008/check_classical.py
python3 research/wu2008/verify_sources.py
python3 research/wu-hf4-audit/measure.py
```

The [phase audit](../research/wu-hf4-audit/README.md) records acceptance, the full
build, literal propositions, axioms and independent kernel replays. The full
build reuses unchanged objects only when receipts and source/object/dependency
hashes match; a forced clean rebuild of every module is not claimed.
