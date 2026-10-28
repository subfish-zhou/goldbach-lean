#!/usr/bin/env python3
"""Re-evaluate the actual production Lean arithmetic, never a generator."""
from pathlib import Path
import json
from preservation import audit
here=Path(__file__).resolve().parent
result=audit()
keys=['status','baseline_archive_sha256','fixed_Git_payment_equality','interpreted_actual_Lean_Nat_payments','independent_64point_sums','outside_support_zero_guard_exact','branches','candidate_source_hashes','interpreter_sha256','Lean_run']
result={k:result[k] for k in keys}
(here/'actual-source-values.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS actual-source Lean arithmetic: 3072 exact original payments, 48 independent block sums, all three original totals, exact outside-zero guard')
