# Portable Hf4 producer V3

The constructive route replaces only its semantic and seed proof templates by their actual strict compiled uniform variants. All three data definitions, DAG operations, 74,200 numeric fields, original 80 bounds, denominator 10^14 and 40 public headers remain unchanged. The checkpoint route retains V2 bytes. Its full project acceptance is still pending.

The 22 relative frozen inputs include the two proof templates and exact old/new SHA lineage. Existing mutation, exact-output, header and relocated read-fence checks apply to both routes. This package reads no retired live source and invokes no Lean. Use `python3 produce.py --route constructive --output-dir DIR` and `--check` as before. Prior producer V2 and unsuccessful proof trials remain preserved.
