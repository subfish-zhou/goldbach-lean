# Wu derived tables and eighth correction audit

This accepted snapshot follows the cumulative-table audit. It retains the
public 1+1.8938 theorem and all original precision and numerical bounds.

Reproduce source sizes and retained interfaces:

```sh
python3 research/wu-derived-audit/measure.py
python3 research/wu-derived-audit/check_values.py
python3 research/wu2008/diagnostics/classical_fourth_certificates.py --check research/wu2008/src
python3 research/wu2008/diagnostics/classical_eighth_correction_certificates.py --check research/wu2008/src
python3 research/wu2008/build.py --all --jobs 1 --lean-threads 2
(cd research/wu2008 && python3 check_classical.py && python3 verify_sources.py)
```

The exact-value check needs the fixed original Git commit recorded in the
script. It reconstructs values from the actual source anchors and checks the
formula definitions; generator checking independently binds generated sources.
The Lean build and independent literal/kernel checks establish the theorem.
Matching receipts may reuse unchanged objects; this was not a forced clean
build. Kernel logs cover the named modules over their accepted imports.

See [the report](../../docs/WU_DERIVED_COMPRESSION.md) for the mathematical
changes, size scope and runtime tradeoff. `validation.json` binds the evidence
files, while `baseline-source-index.json` records the preceding accepted tree.
