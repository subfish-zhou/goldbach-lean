#!/usr/bin/env python3
"""Check rejection paths using disposable copies; never mutate production sources."""
from pathlib import Path
import importlib.util
import json
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('eighth_values', HERE/'check_values.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
original = audit.SRC
report_path = HERE/'eighth-values.json'
if not report_path.exists():
    raise SystemExit('PENDING: run the production-source numerical audit first')
report = json.loads(report_path.read_text())
names = set(report['current_source_sha256']) | {
    name+'.lean' for name in report['frozen_shared_source_sha256']}
sources = {name: (original/name).read_text() for name in names}
first_sum = str(report['block_sums'][0])
cases = [
    ('shared_horner', 'WR2IntegerLogHorner.lean', '334639305*Q^11', '334639306*Q^11', 'Frozen shared module changed: WR2IntegerLogHorner'),
    ('spurious_25_factor', 'WR2IntegerLogUpper.lean', '2*commonDen*p^25', '2*commonDen*p^25/25', 'Lean formula changed: hiNumerator'),
    ('shared_ceil', 'WR2ClassicalCumulativeDivision.lean', '(n+d-1)/d', '(n+d)/d', 'Frozen shared module changed: WR2ClassicalCumulativeDivision'),
    ('grid_formula', 'WR2ClassicalEighthRawIntegerData.lean', '1228800+1027', '1228800+1028', 'Lean formula changed: gridNumerator'),
    ('quotient_guard', 'WR2ClassicalEighthRawIntegerData.lean', 'if i < 2048 then', 'if i < 2047 then', 'Lean formula changed: paymentNumerator'),
    ('block_sum_target', 'WR2ClassicalEighthRawSums.lean', first_sum, str(int(first_sum)+1), 'Block target mismatch'),
    ('total_target', 'WR2ClassicalEighthRawPayments.lean', '5258450040652036', '5258450040652037', 'Total statement changed'),
]
results = []
for label, name, old, new, expected in cases:
    if old not in sources[name]:
        raise ValueError(f'Negative-control fixture no longer matches: {label}')
    with tempfile.TemporaryDirectory(prefix='eighth-audit-negative-') as directory:
        audit.SRC = Path(directory)
        for filename, text in sources.items():
            (audit.SRC/filename).write_text(text.replace(old, new, 1) if filename == name else text)
        try:
            audit.check_eighth()
        except ValueError as error:
            if expected not in str(error):
                raise ValueError(f'Unexpected rejection for {label}: {error}') from error
            results.append({'case': label, 'rejected': True, 'reason': str(error)})
        else:
            raise ValueError(f'Corruption was accepted: {label}')
audit.SRC = original
(HERE/'negative-controls.json').write_text(json.dumps({
    'validation_scope': 'Python audit rejection paths only; no Lean or production writes',
    'cases': results, 'all_rejected': True}, indent=2)+'\n')
print(f'PASS: all {len(results)} numerical-audit negative controls rejected; production source unchanged.')
