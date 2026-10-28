# Light numeric layer acceptance audit

Reproduce source checks from the repository root:

```sh
python3 research/wu-light-layer-audit/measure.py
python3 research/wu-light-layer-audit/preservation.py
python3 research/wu-light-layer-audit/negative_controls.py
python3 research/wu2008/diagnostics/classical_c_eighth_certificates.py --check research/wu2008/src
python3 research/wu2008/diagnostics/classical_sixth_certificates.py --check research/wu2008/src
python3 research/wu2008/diagnostics/classical_fourth_certificates.py --check research/wu2008/src
python3 research/wu2008/build.py --all --jobs 1 --lean-threads 2 --timeout 1200
(cd research/wu2008 && python3 check_classical.py && python3 verify_sources.py)
```

Frozen records bind the prior accepted sources and 104 complete individual
proofs. Source comparisons and negative controls supplement Lean checking.
The validation record lists independent kernel replay scope and evidence
fingerprints. See [the report](../../docs/WU_LIGHT_NUMERIC_LAYERS.md).
