#!/usr/bin/env python3
"""Exercise audit rejection paths using disposable source copies only."""
from pathlib import Path
import importlib.util
import json
import tempfile

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('sixth_values', HERE/'check_values.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
original = audit.SRC
names = ['WR2IntegerLogHorner.lean', 'WR2ClassicalSixthIntegerData.lean',
         'WR2ClassicalSixthLowerSums.lean', 'WR2ClassicalSixthUpperSums.lean',
         'WR2ClassicalSixthLowerPayments.lean', 'WR2ClassicalSixthUpperPayments.lean']
sources = {name: (original/name).read_text() for name in names}
report = json.loads((HERE/'sixth-values.json').read_text())
first_sum = str(report['families']['lower']['block_sums'][0])
cases = [
    ('shared_horner', names[0], '334639305*Q^11', '334639306*Q^11', 'Shared Horner changed'),
    ('grid_formula', names[1], '576151552+12575', '576151552+12576', 'Lean formula changed: gridNumerator'),
    ('quotient_guard', names[1], 'if i < 4096 then', 'if i < 4095 then', 'Lean formula changed: paymentNumerator'),
    ('consumer_branch', names[1], 'lowerNumerator := SixthIntegerPayment.paymentNumerator false',
     'lowerNumerator := SixthIntegerPayment.paymentNumerator true', 'Lean formula changed: lowerNumerator'),
    ('block_sum_target', names[2], first_sum, str(int(first_sum)+1), 'lower block target mismatch'),
    ('total_target', names[5], '1025832247091325', '1025832247091326', 'upper total statement changed'),
]
results = []
for label, name, old, new, expected in cases:
    if old not in sources[name]:
        raise ValueError(f'Negative-control fixture no longer matches: {label}')
    with tempfile.TemporaryDirectory(prefix='sixth-audit-negative-') as directory:
        audit.SRC = Path(directory)
        for filename, text in sources.items():
            (audit.SRC/filename).write_text(text.replace(old, new, 1) if filename == name else text)
        try:
            audit.check_sixth()
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
