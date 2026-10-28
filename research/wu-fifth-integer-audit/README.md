# Fifth integer payment acceptance audit

Reproduce from the repository root:

```sh
python3 research/wu-fifth-integer-audit/measure.py
python3 research/wu-fifth-integer-audit/preservation.py
python3 research/wu-fifth-integer-audit/actual-source-values.py
python3 research/wu-fifth-integer-audit/negative_controls.py
python3 research/wu2008/diagnostics/classical_fifth_certificates.py --check research/wu2008/src
python3 research/wu2008/diagnostics/classical_c_eighth_certificates.py --check research/wu2008/src
python3 research/wu2008/diagnostics/classical_sixth_certificates.py --check research/wu2008/src
python3 research/wu2008/diagnostics/classical_fourth_certificates.py --check research/wu2008/src
python3 research/wu2008/build.py --all --jobs 1 --lean-threads 2 --timeout 1200
(cd research/wu2008 && python3 check_classical.py && python3 verify_sources.py)
```

Frozen records bind the previous accepted inventory, original payment tables,
public statements and all sources outside the Fifth scope. The actual-source
interpreter checks all 3,072 values and 48 block sums. Negative controls verify
that relevant alterations are rejected. These checks supplement Lean checking.
The validation record lists kernel scopes, tool/source hashes and logs. Older
acceptance directories remain unchanged historical records.
See [the report](../../docs/WU_FIFTH_INTEGER_PAYMENTS.md).
