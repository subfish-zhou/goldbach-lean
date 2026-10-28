# Hf4 shared certificate audit

This accepted snapshot preserves the public 1+1.8938 result and all original
numerical certificate values and panel bounds.

From the repository root:

```sh
python3 research/wu-shared-audit/measure.py
python3 research/wu-shared-audit/check_values.py
python3 research/wu2008/diagnostics/hf4_compact_certificates.py --output-dir research/wu2008/src --check
python3 research/wu2008/build.py --all --jobs 1 --lean-threads 2
(cd research/wu2008 && python3 check_classical.py && python3 verify_sources.py)
```

`baseline_generator.py` is the small historical generator, not copied numerical
certificate data. Its regenerated old source hashes must match the accepted
baseline before the actual new source fields are compared. Python arithmetic
uses exact fractions. Lean checks remain independently necessary.

`validation.json` binds the evidence. Kernel logs cover named modules over
accepted imports; source/dependency receipts can reuse unchanged objects.
See [the report](../../docs/WU_SHARED_CERTIFICATES.md) for scope and timings.
