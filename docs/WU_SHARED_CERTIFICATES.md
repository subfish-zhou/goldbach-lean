# Hf4 shared certificates and exact arithmetic operations

This phase follows [derived-table compression](WU_DERIVED_COMPRESSION.md).
It preserves the public 1+1.8938 result, every one of the 76,200 rational
coefficient/error fields, all 40 original panel bounds, and the original
1/40 half-width and 10^-14 coefficient/error rounding scale.

## Mathematical simplification

The 381-node expression graph contains 49 nodes independent of the panel.
Their certificates and proofs are now shared once, with universal panel
parameters, instead of being repeated forty times.

Exact operations supply further certificates directly from their parents:

- addition adds the four cubic coefficients and error bounds;
- negation negates the coefficients and preserves the error;
- scalar multiplication multiplies coefficients by the scalar and error by
  its absolute value.

The generator selects these operations only where all five resulting rational
fields equal the previously accepted certificate. The one addition and seven
constant-multiplication nodes that involve actual rounding retain their stored
certificates. The exact scale rule handles negative scalars as well.

Across the shared and per-panel modules, literal records fall from 15,240 to
6,204: **9,036 repeated or algebraically determined records disappear**. Derived
expressions and shared models still provide all 15,240 original certificates;
no analytic term or error allowance is dropped. The expression graph, original
rational-model soundness module, integration bridge and final theorem source
remain byte-identical. The 80 retained `compact_model`/`mass_bounds` statements
are unchanged, while unused internal panel-local names need not be retained.

## Measured size

| Scope | Effective lines before | Effective lines after | Net reduction |
|---|---:|---:|---:|
| Full local Wu tree | 625,805 | 620,401 | 5,404 |
| Final theorem import closure | 585,051 | 579,647 | 5,404 |

The phase removes 7,311 physical lines and 908,008
UTF-8 bytes, including the two new common modules. The full tree has 4,643
modules and 724,235 physical lines; the theorem closure has
4,256 modules and 677,757 physical lines.
The cumulative closure saving is 546,989 effective lines from the original
version. These are module-level source counts excluding external Lake packages,
Python generators, documentation and audit material, not minimal proof lengths.

## Validation and runtime

The complete 4,643-module source/receipt build passes, as do both independent
literal statements (1.8938 and 1.894), the standard-axiom checks and source
verification. Independent kernel replays cover both new common modules,
Panel0, Batch12, the aggregate and the final theorem over accepted imports.
Unchanged objects are reused only with matching source/dependency receipts;
this was not a forced clean build. The 17-file generator check passes.

The audit regenerates the previous 15 sources from a small archived, standalone
generator and checks every byte hash against the accepted baseline. It then
parses the actual new source, binds the exact operators to their Lean definitions,
and independently reconstructs all 76,200 rational fields using exact fractions.
This numerical comparison complements rather than replaces Lean verification.

Single-run wall-clock comparisons on the same machine were 28.233 -> 13.566
seconds for Panel0 and 76.032 -> 52.888 seconds for Batch12. These trials used
one compilation process with two Lean threads; they are not controlled repeated
benchmarks or a general speed guarantee. They showed no representative
normalization regression before adoption. No constant was retuned.

See [the reproducible audit](../research/wu-shared-audit/README.md).
