# Verification

Run all commands at the project root with the pinned toolchain:

```sh
lake exe cache get
lake build
python3 scripts/check.py
lake env leanchecker --verbose Goldbach.Theorem
```

## Separate acceptance gates

1. **Source build:** `lake build` compiles all four default libraries, including
   the public entry point, acceptance checks, and every shipped Lean module.
2. **Source surface:** `python3 scripts/check.py --static-only` checks all shipped
   Lean files for missing local imports, import cycles, source reachability,
   proof placeholders, custom axiom declarations, trusted native decision calls,
   unsafe declarations, and the kernel-check bypass option. It also checks the
   release text for untranslated CJK content and private machine paths, including
   Blueprint source and renderer configuration. The isolated `Goldbach.Blueprint`
   documentation root is checked separately from the public import closure.
3. **Literal target and axiom dependency:** `python3 scripts/check.py` performs
   the source checks and elaborates `Goldbach/Checks.lean`. The check module
   expands the public specification, verifies the original implementation
   signatures, and prints the transitive axioms of the two public results and
   their implementation endpoints. The script fails on absent reports or axioms
   outside `propext`, `Classical.choice`, and `Quot.sound`.
4. **Independent replay:** `lake env leanchecker --verbose Goldbach.Theorem`
   replays compiled declarations in a separate process with the matching Lean
   checker. Use an environment without an inherited `LEAN_PATH` from another
   project. Success on a leaf alone does not replace the source build.
5. **Isolated reconstruction:** extract the source archive into an independent
   directory, fetch the pinned dependencies, and run the same commands. Do not
   copy project `.olean` files from the development tree.

`python3 scripts/check.py --static-only --count-lines` additionally reports
nonblank Lean source lines with nested comments removed and string literals
retained. This is the release-note size convention, not a proof verification gate.

## What these checks do not mean

The lexical scanner understands nested comments and strings but is not a Lean
parser. The compiler and the axiom report are the authoritative proof checks.
No finite numerical experiment establishes the universal theorem: the theorem
is a Lean proof with an existential threshold. The standard axiom report does
not on its own establish that a named predicate matches the intended mathematics;
that is why the literal target and almost-prime conversion are checked separately.

No unqualified claim of a warning-free codebase is made: existing proof-style
linter warnings are distinct from proof holes, build errors, and unexpected axioms.
