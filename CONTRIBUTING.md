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
