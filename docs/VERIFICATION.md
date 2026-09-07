# Verification

Run all commands at the project root with the pinned toolchain:

```sh
unset LEAN_PATH LEAN_SRC_PATH
lake exe cache get
lake --wfail build
python3 scripts/check.py
lake env leanchecker --verbose Goldbach.Theorem
```

For a focused build use `lake build Goldbach.Theorem` (1+2),
`lake build Goldbach.OnePlusOneNine` (1+1.9), or `lake build Goldbach.All`
(both interfaces). Keep `.lake/` during upgrades so Lake can reuse unchanged
artifacts; see the [upgrade instructions](../README.md#focused-builds-and-upgrading-an-existing-checkout).

`python3 scripts/check.py` runs both acceptance probes. The option
`--one-two-only` runs the original Chen probe while retaining the full source
scan. The Li–Liu probe is `Goldbach/OnePlusOneNineChecks.lean`.

## Li–Liu endpoint inspection

After building `Goldbach.OnePlusOneNine`, the following commands in a Lean file
inspect all four public declarations and their transitive axiom dependencies:

```lean
import Goldbach.OnePlusOneNine

#check Goldbach.one_plus_one_nine
#check Goldbach.one_plus_one_nine_real
#check Goldbach.one_plus_one_nine_count
#check Goldbach.one_plus_one_nine_lower_bound
#print axioms Goldbach.one_plus_one_nine
#print axioms Goldbach.one_plus_one_nine_real
#print axioms Goldbach.one_plus_one_nine_count
#print axioms Goldbach.one_plus_one_nine_lower_bound
```

Run the file with `lake env lean path/to/check.lean`. Compare the displayed types
with [THEOREMS.md](THEOREMS.md): retain `r^10 ≤ q^9`, the count of distinct actual
primes `p`, the strict coefficient `1/2500`, and the choice of
`κ < 515093/800000000` before the threshold. The allowed logical axioms are
`propext`, `Classical.choice` and `Quot.sound`.

A separate module replay is available with:

```sh
lake env leanchecker --verbose Goldbach.OnePlusOneNine
```

This replays the new facade over its cached imports. To replay all four project
libraries after a full build, use:

```sh
lake env leanchecker --verbose Goldbach MathlibNt AnalyticNumberTheory PrimeNumberTheoremAnd
```

The pinned checker expands these module-name prefixes; the pinned Mathlib
artifacts supply the external dependency environment. Historical Chen comparator
and replay records retain their original 1+2 scope.

## Acceptance gates

1. **Source build:** `lake --wfail build` builds all four default libraries,
   covering all shipped project-proof modules, both public interfaces and the acceptance
   checks. Lean elaborates the source and its kernel checks the resulting proof
   terms as modules are compiled.
2. **Source surface:** `python3 scripts/check.py --static-only` scans all shipped
   Lean files for missing local imports, import cycles and source reachability.
   It flags the tokens `sorry`, `admit`, `axiom`, `native_decide`, `unsafe` and
   `debug.skipKernelTC` after masking nested comments and string literals.
   These rules catch proof placeholders, custom axiom declarations, trusted
   native decision calls, unsafe declarations and the kernel-check bypass option
   at the source level. The release-text scan also checks for untranslated CJK
   content and private machine paths, including Blueprint source and renderer
   configuration. `Goldbach.Blueprint` is a separate documentation root in the
   reachability check, alongside the public and check roots.
3. **Literal targets and axiom dependencies:** `python3 scripts/check.py` runs
   the source checks and elaborates two separate probes. `Goldbach/Checks.lean`
   expands the Chen specification, verifies its implementation signatures,
   quantitative coefficient, normalization and actual representation count, and
   checks repeated prime factors and the second summand's lower bound. Its four
   axiom reports cover the two Chen public results and their implementation
   endpoints. `Goldbach/OnePlusOneNineChecks.lean` checks the four Li–Liu public
   results and reports their axioms. Every expected report must appear exactly
   once, and every reported axiom must belong to the allowed set
   `propext`, `Classical.choice`, `Quot.sound`.
4. **Independent module replay:** `lake env leanchecker --verbose Goldbach.Theorem`
   uses the matching Lean checker in a separate process to replay compiled
   declarations in `Goldbach.Theorem` over its cached imports. The imports supply
   the dependency environment for this module-level replay; the full source
   build above checks the project's source closure. Run the replay in an
   environment with `LEAN_PATH` and `LEAN_SRC_PATH` clear of values inherited
   from another project. CI also replays `Goldbach.Checks`,
   `Goldbach.OnePlusOneNine`, `Goldbach.OnePlusOneNineChecks` and `Goldbach.All`
   as separate modules over their cached imports.
5. **Isolated reconstruction:** extract the source archive into an independent
   directory, fetch the pinned dependencies, and run the same commands. Build
   project `.olean` files from the extracted sources in that directory; obtain
   dependency artifacts through the pinned dependency setup.

The logical foundation is Lean's standard propositional extensionality
(`propext`), classical choice (`Classical.choice`) and quotient soundness
(`Quot.sound`). The axiom gate accepts any subset of these three and rejects
additional axioms, missing reports and duplicate reports. `check.py` clears
inherited `LEAN_PATH` and `LEAN_SRC_PATH` before invoking Lean.

## How the checks fit together

The lexical scanner checks source tokens and import structure. It handles nested
comments and strings; Lean's parser, elaborator and kernel handle Lean syntax,
types and proof terms. The axiom reports identify the transitive logical
assumptions used by each endpoint. The literal target checks establish the types
of the public results, and the proved almost-prime conversion connects the
internal representation predicate to primes and products of two primes.
Together these checks cover the implementation, its logical dependencies and
its public mathematical statement.

The existence theorems quantify over every even natural number above an
existential threshold. Their universal scope comes from the Lean proofs. The threshold and
quantifier order are given in [THEOREMS.md](THEOREMS.md).

The release build uses `lake --wfail build`: every reported warning fails the
build, including warnings replayed from cached modules. The public statement
check also enables `warningAsError`. Resolve each warning at its source and
keep the warning gate active alongside the theorem-type and axiom checks.

## Source size and website checks

`python3 scripts/check.py --static-only --count-lines` additionally reports
nonblank Lean source lines with nested comments removed and string literals
retained. Release notes use this convention to measure source size.

The documentation pipeline checks generated module coverage, declaration search
anchors, local links and site routes. Its source-only regression tests include
API-only and legacy-bundle assembly inputs and deployment-boundary checks.
See [DOCUMENTATION.md](DOCUMENTATION.md) for the commands and browser checks.
