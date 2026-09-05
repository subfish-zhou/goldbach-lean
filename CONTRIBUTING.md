# Contributing

Keep changes local until they have been reviewed. Use the pinned toolchain and
lockfile; do not silently update dependencies as part of proof cleanup.

For proof changes, preserve the exact quantifiers, parameter ranges, and public
target. Do not introduce proof placeholders, custom axioms, `native_decide`,
or kernel-check bypasses. Build the changed module and then the public root,
and rerun the public theorem checks.

For documentation and restructuring, preserve mathematical explanations,
source attributions, and copyright notices. Use English throughout the shipped
project. Keep logs, caches, exploratory proofs, and internal task documents out
of the release tree. New modules should have focused responsibilities and an
acyclic import graph. Move reusable lemmas below their consumers rather than
introducing duplicate copies.

Before proposing a change, run:

```sh
lake build
python3 scripts/check.py
python3 -m unittest discover -s scripts -p 'test_*.py'
```
