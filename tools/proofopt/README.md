# Proof optimization tools

This is a read-only discovery pipeline plus isolated proof-proposal tools. It is
not a theorem prover, an automatic refactoring service, or an admission policy
based on similarity scores. Production mathematical modules never import these
tools.

## Inputs and trust boundary

Use one **known matching** source revision, Lean toolchain, package manifest and
compiled-object seed. `manifest` hashes source, `.ilean`, `.olean`, and available
`.olean.server`/`.olean.private` parts; it freezes inputs but cannot establish
that an arbitrary object was compiled from an arbitrary source. Recompile the
selected original sources before accepting a replacement, and compare their
original declarations against the seed.

`LEAN` below is the absolute path of that toolchain's `lean` executable.
`SEED_OBJECTS` is the project object directory. `SEED_LEAN_PATH` includes it and
the matching dependency object directories, separated by colons. Obtain these
from the existing verified build environment; do not copy Mathlib or create a
shared writable build directory. `OUT` must be a new, private evidence directory.

```sh
python3 tools/proofopt/index.py manifest \
  --source "$PWD" --objects "$SEED_OBJECTS" --output "$OUT/manifest.json"
python3 tools/proofopt/run_extract.py \
  --manifest "$OUT/manifest.json" --lean "$LEAN" \
  --lean-path "$SEED_LEAN_PATH" --output "$OUT/declarations.jsonl" --timeout 1200
python3 tools/proofopt/index.py index \
  --manifest "$OUT/manifest.json" --input "$OUT/declarations.jsonl" \
  --output "$OUT/index.sqlite"
python3 tools/proofopt/index.py candidates \
  --database "$OUT/index.sqlite" --min-lines 12 --limit 100 \
  --output "$OUT/candidates.json"
```

The extractor emits declaration types, universe parameters, proof/type
fingerprints, structural sizes and dependency names. Local binder spelling is
ignored for discovery; constants are retained in the type fingerprint and
abstracted in the coarse shape fingerprint. No fingerprint is an equality
certificate. The original expressions remain in the pinned compiled objects.

Source locations come from the compiler's `.ilean` declaration inventory. The
Python reader implements its UTF-16/LSP positions, including astral characters,
CRLF and end-of-file ranges. `SourceSpan.lean` subsequently uses Lean's command
parser to locate the actual proof body; it rejects equation-style and `where`
declarations rather than guessing their boundaries.

Only a successful extractor invocation with checked per-module completion
receipts can produce a sealed stream. The index rejects unsealed/truncated
streams, wrong module counts, changed input bytes, conflicting same-module
records, and incomplete databases. Cross-module repeated names are retained as
separate occurrences, their dependency edges are unioned conservatively, and
they are excluded from targets/providers. They are **not** silently equated.

## Bounded coverage and proposal generation

First compile and exercise the tools in private outputs:

```sh
python3 -m unittest discover -s tools/proofopt -p 'test_*.py'
python3 tools/proofopt/test_lean.py --lean "$LEAN" \
  --lean-path "$SEED_LEAN_PATH" --output "$OUT/tool-tests"
python3 tools/proofopt/run_coverage.py \
  --candidates "$OUT/candidates.json" --lean "$LEAN" \
  --lean-path "$OUT/tool-tests:$SEED_LEAN_PATH" \
  --output "$OUT/coverage" --limit 20 --timeout 300
```

The current retrieval stage considers equal type fingerprints and equal full
structural shapes among explicit project theorems. This deliberately misses
many general-to-special relationships; it is not an exhaustive containment
search. A declaration's source length is only a ranking feature, **not an
estimate of saved proof lines**. Long signatures and already-short wrappers can
rank highly and must be discarded if there is no actual saving.

The Lean probe restores state between pairs, keeps original universes rigid,
checks reverse type/proof dependencies (including generated helpers), and tries
`apply`, local assumptions, reflexivity and a bounded `simp only [*]` closure.
Every successful proof is checked by the kernel and then printed and
re-elaborated independently. Generated replay terms may retain unused binder
names, so only the unused-variable **style** linter is disabled in that replay;
this is not an exception for production source builds. Failures and timeouts are
not successes, and no admission receipt is written if text replay fails.

Select a unique successful provider for a target, then generate a proposal:

```sh
python3 tools/proofopt/propose.py \
  --database "$OUT/index.sqlite" --results "$OUT/coverage/results.json" \
  --target 'Namespace.targetTheorem' --source "$PWD" \
  --lean "$LEAN" --lean-path "$OUT/tool-tests:$SEED_LEAN_PATH" \
  --recipe exact --output "$OUT/proposal"
```

The proposal is a complete source file in the private output directory, never an
in-place edit. `exact`, `apply` and `discharge` are explicit recipe choices. A
coverage proof at the full theorem type does not guarantee that every source
recipe works beneath the declaration's existing binders. Compile it, retain the
failure evidence, and choose an explicit short adapter. Do not retain broad
search tactics or unused tactic tails merely to keep an automated recipe.

## Admission, not just discovery

A candidate may be installed only after all of the following:

1. Recompile the selected original source against the seed. Compile changed
   source with `autoImplicit=false` and `warningAsError=true` in private outputs.
   Untouched legacy sources retain the repository's existing implicit-binder
   setting. If an old implicit binder is made explicit, its compiled type must
   still be identical.
2. Use `Compare.lean` to compare **actual** full types, universe parameters and
   retained definition values, not fingerprints. Pass explicit original names:
   `lean --run tools/proofopt/Compare.lean old.olean new.olean names.txt`.
3. Jointly import the changed modules, enumerate their new and private
   declarations as well as public endpoints, and use `Audit.lean` to enforce the
   standard axiom set `propext`, `Classical.choice`, `Quot.sound`. No additional
   mathematical premise is admitted.
4. Check actual value-dependency paths from consumers to the reused theorem.
   Import reachability alone is insufficient. If a lower existing producer is
   private, an explicitly reviewed public interface in that lower module may
   be preferable to importing an unrelated higher-level application.
5. Recompile affected immediate consumers and public entrypoints; compare the
   public contracts again. Use matching-toolchain `leanchecker --verbose` on
   changed modules and theorem endpoints. This is separate from compiling a
   generated replacement term.
6. Account for the entire mathematical change: new interfaces, adapters and
   imports are included. Report tooling, tests and documentation separately;
   adding a discovery tool is not a whole-repository line reduction.

Never run Lake against an overlay containing writable-through links into the
seed. Private object overlays must omit every file to be regenerated, and
selected modules must be built in dependency order (including dependencies
through unselected intermediate modules). Source/object hashes and the actual
commands and exit statuses belong in the external acceptance receipt.

## Deliberate limits

No automatic source installation, deletion, commit, push, tag movement, macro
compression, unproved mathematical assumption, whole-library unfolding,
embedding-based correctness criterion, or automatic lower-module design.
Proof anti-unification, broad semantic coverage retrieval and representation
normalization remain later stages, not claimed features of this first version.
