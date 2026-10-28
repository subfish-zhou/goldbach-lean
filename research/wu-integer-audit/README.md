# Integer payment compression audit

The accepted phase retains the original twelve-term logarithms, midpoint grids,
10^12 payment scale and public 1+1.8938 theorem.

From the repository root:

```sh
python3 research/wu-integer-audit/measure.py
python3 research/wu-integer-audit/check_values.py
python3 research/wu2008/diagnostics/classical_c_eighth_certificates.py --check research/wu2008/src
python3 research/wu2008/diagnostics/classical_sixth_certificates.py --check research/wu2008/src
python3 research/wu2008/build.py --all --jobs 1 --lean-threads 2
(cd research/wu2008 && python3 check_classical.py && python3 verify_sources.py)
```

The value audit reads original tables from immutable Git commit
`c4e1b8d00dda9661140f95e0f03f0d5a08d636c2` and checks their SHA fingerprints.
Exact Python arithmetic complements the Lean proofs; it does not replace them.
`source-size.json` records retained statements and explicitly retired internal
helpers. `validation.json` binds the accepted evidence and lists kernel replay
scope. Unchanged dependency objects require matching build receipts.

See [the report](../../docs/WU_INTEGER_PAYMENTS.md).
