# Contributing

Keep changes local until they have been reviewed. Use the pinned toolchain and
lockfile. Identify dependency updates explicitly in the proposed change,
including any updates needed during proof cleanup.

For proof changes, preserve the exact quantifiers, parameter ranges, and public
target. Every proof must pass Lean's kernel checking and be free of proof
placeholders, custom axioms, `native_decide`, and kernel-check bypasses. Build
the changed module and then the public root, and rerun the public theorem checks.
Keep linters enabled and resolve every reported warning; continuous integration
treats build warnings as failures.

Keep the 1+2 and 1+1.9 public imports separate: `Goldbach` retains the Chen
interface, `Goldbach.OnePlusOneNine` exposes Li–Liu, and `Goldbach.All` combines
them. Build `Goldbach.Theorem` or `Goldbach.OnePlusOneNine` for a focused change,
then `Goldbach.All` and the full project for integration. Preserve the literal
`r^10 ≤ q^9` condition, the count of distinct primes `p`, the strict `1/2500`
bound, and the order “fix `κ < 515093/800000000`, then choose the threshold”.
The [verification guide](docs/VERIFICATION.md) distinguishes the existing Chen
checks from the separate Li–Liu probe and endpoint inspection.

Existing builds can reuse unchanged dependencies with the pinned configuration.
Keep `.lake/` during ordinary upgrades and let Lake determine which modules
need rebuilding; the [README](README.md#focused-builds-and-upgrading-an-existing-checkout)
gives update and target-selection commands.

For documentation and restructuring, preserve mathematical explanations,
source attributions, and copyright notices. Use English throughout the shipped
project. Keep logs, caches, exploratory proofs, and internal task documents out
of the release tree. New modules should have focused responsibilities and an
acyclic import graph. Place reusable lemmas in shared dependencies below their
consumers and reuse those declarations across the project.

The project website has a standalone homepage at `/`, Lean API documentation at
`/docs/`, and the Blueprint at `/blueprint/`, relative to the project site root.
Keep navigation consistent with these locations. Extract Blueprint data with
`lake --wfail build Goldbach:blueprint`.

Before proposing a change, run:

```sh
lake --wfail build
python3 scripts/check.py
python3 -m unittest discover -s scripts -p 'test_*.py'
```
