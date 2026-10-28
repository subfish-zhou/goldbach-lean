#!/usr/bin/env python3
"""Exercise Bq numerical-audit rejection paths on disposable source copies."""
from pathlib import Path
import importlib.util
import json
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('bq_values', HERE/'check_values.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
original = audit.SRC
report_path = HERE/'bq-values.json'
if not report_path.exists():
    raise SystemExit('PENDING: run the production-source numerical audit first')
report = json.loads(report_path.read_text())
names = set(report['current_source_sha256']) | {
    name+'.lean' for name in report['frozen_shared_source_sha256']}
sources = {name: (original/name).read_text() for name in names}
data = 'WR2ClassicalFourthDataBq.lean'
cases = [
    ('shared_horner', 'WR2IntegerLogHorner.lean', '334639305*Q^11', '334639306*Q^11', 'Frozen shared module changed: WR2IntegerLogHorner'),
    ('spurious_25_factor', 'WR2IntegerLogUpper.lean', '2*commonDen*p^25', '2*commonDen*p^25/25', 'Frozen shared module changed: WR2IntegerLogUpper'),
    ('shared_ceil', 'WR2ClassicalCumulativeDivision.lean', '(n+d-1)/d', '(n+d)/d', 'Frozen shared module changed: WR2ClassicalCumulativeDivision'),
    ('numerator_formula', data, '1000000000000000*4000', '1000000000000000*4001', 'Lean formula changed: BqRawNumerator'),
    ('denominator_formula', data, '(8000+i)*', '(8001+i)*', 'Lean formula changed: BqRawDenominator'),
    ('support_guard', data, 'if i ≤ 10540 then', 'if i ≤ 10541 then', 'Lean formula changed: Bq'),
    ('zero_rounding', data, 'ClassicalCumulativeDivision.ceilDiv (BqRawNumerator i) (BqRawDenominator i)',
     'BqRawNumerator i/BqRawDenominator i+1', 'Lean formula changed: Bq'),
]
results = []
for label, name, old, new, expected in cases:
    if old not in sources[name]:
        raise ValueError(f'Negative-control fixture no longer matches: {label}')
    with tempfile.TemporaryDirectory(prefix='bq-audit-negative-') as directory:
        audit.SRC = Path(directory)
        for filename, text in sources.items():
            (audit.SRC/filename).write_text(text.replace(old, new, 1) if filename == name else text)
        try:
            audit.check_bq()
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
