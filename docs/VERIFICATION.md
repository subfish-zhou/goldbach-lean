# Verification

Run all commands at the project root with the pinned toolchain:

```sh
unset LEAN_PATH LEAN_SRC_PATH
lake exe cache get
lake --wfail build
python3 scripts/check.py
lake env leanchecker --verbose Goldbach.Theorem
```

## Acceptance gates

1. **Source build:** `lake --wfail build` builds all four default libraries,
   covering every shipped Lean module, the public entry point and the acceptance
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
   the source checks and elaborates `Goldbach/Checks.lean`. The check module
   expands the public specification, verifies the original implementation
   signatures, and checks the quantitative coefficient, normalization and actual
   representation count. It also checks repeated prime factors and the lower
   bound on the second summand. Its four axiom reports cover the two public
   results and their implementation endpoints. Every report must appear exactly
   once, and each reported axiom must belong to the allowed set
   `propext`, `Classical.choice`, `Quot.sound`.
4. **Independent module replay:** `lake env leanchecker --verbose Goldbach.Theorem`
   uses the matching Lean checker in a separate process to replay compiled
   declarations in `Goldbach.Theorem` over its cached imports. The imports supply
   the dependency environment for this module-level replay; the full source
   build above checks the project's source closure. Run the replay in an
   environment with `LEAN_PATH` and `LEAN_SRC_PATH` clear of values inherited
   from another project.
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

The theorem quantifies over every even natural number above an existential
threshold. Its universal scope comes from the Lean proof. The threshold and
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
