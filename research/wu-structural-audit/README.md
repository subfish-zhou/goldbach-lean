> Historical accepted snapshot. Current integration and acceptance are in [the Hf4 audit](../wu-hf4-audit/README.md).

# Structural simplification audit

Current report: [Wu structural simplification](../../docs/WU_STRUCTURAL_SIMPLIFICATION.md).
This phase follows the preserved [1.8938 compression snapshot](../wu18938-audit/README.md).

The integrated proof changes only `WSrcFifthGainAnalyticEnvelope` and its diagnostic
root: the same first-order logarithm inequality now follows directly from a
standard analytic inequality, without first deriving a seventh-order envelope.
All other 4,769 source files, including numerical tables, are byte-identical.

- `baseline-source-index.json` records pre-phase source hashes, counts and imports.
- `baseline/` preserves the two original changed files for review.
- `source-size.json` distinguishes full-tree deletion (9 effective lines) from
  theorem-closure reduction (425 effective lines, 5 fewer imported modules).
- `full-build.log` records the accepted 4,771-module build. Matching build receipts
  permit unchanged objects to be reused; this is not a forced clean rebuild.
- `classical-acceptance.json`, `literal-check.log` and `classical-literal-axioms.log`
  record exact 1.8938 and legacy 1.894 acceptance using only standard axioms.
- The two `kernel-*.log` files record separate replays of the changed analytic
  module and final theorem over accepted imports, not individual replays of all imports.
- `weighted-analysis.md` and `weighted_check.py` record the rejected dual/max
  changes and exact rational diagnostics; these are not new Lean proofs.
- `hf4/Hf4SeriesEnvelope.lean` is an isolated, checked mathematical candidate.
  It proves valid logarithm envelopes and domination of old envelopes. It is
  **not** imported into the accepted theorem or included in compression counts.
  Its four standard-axiom reports are in `hf4/build.log`.
- `hf4/symbolic-check.py` (requires SymPy) independently reproduces factorizations
  and the exact counterexample to removing the lower split. Expression operation
  counts do not measure Lean DAG size or actual code savings.

From the repository root, after the Wu build:

```sh
python3 research/wu-structural-audit/measure.py
python3 research/wu-structural-audit/weighted_check.py
python3 research/wu-structural-audit/check_experiment.py
```

The full acceptance commands are:

```sh
python3 research/wu2008/build.py --all --jobs 6 --lean-threads 2
python3 research/wu2008/check_classical.py
python3 research/wu2008/verify_sources.py
```

`validation.json` binds the recorded evidence to source-manifest and artifact
hashes. Historical audits retain their own original scope and accepted hashes.
