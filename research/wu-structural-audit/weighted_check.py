#!/usr/bin/env python3
"""Read-only exact matrix and hypothetical dependency audit."""
from pathlib import Path
from fractions import Fraction
import re
import json

root = Path(__file__).resolve().parents[1] / 'wu2008/src'
text = (root / 'WR2XiRationalCandidate.lean').read_text()
matrix_text = text.split('def lowerMatrix', 1)[1].split('/-- Rational subsolution', 1)[0]
rows = re.findall(r'!\[([^\[\]]+)\]', matrix_text)
matrix = [[Fraction(x.strip()) for x in row.split(',')] for row in rows]
assert len(matrix) == 9 and all(len(row) == 9 for row in matrix)
assert all(x > 0 for row in matrix for x in row)
sums = list(map(sum, matrix))
assert max(sums) == Fraction(199, 500)
files = {f.stem: f for f in root.glob('*.lean')}
graph = {n: re.findall(r'^import (\w+)', f.read_text(), re.M) for n, f in files.items()}
def closure(graph, root):
    found, todo = set(), [root]
    while todo:
        node = todo.pop()
        if node in found or node not in graph:
            continue
        found.add(node)
        todo.extend(graph[node])
    return found
old = closure(graph, 'WR2ClassicalCertificate')
# Hypothetical only: change the source-sixth import from max-vector count
# to the direct candidate certificate. No source file is edited.
modified = dict(graph)
modified['WR2XiSourceSixth'] = ['W01ContinuousCount', 'WR2XiCandidateCertificate']
new = closure(modified, 'WR2ClassicalCertificate')
lost = old - new
result = {
    'matrix_all_entries_strictly_positive': True,
    'row_sums': [str(x) for x in sums],
    'maximum_row_sum': str(max(sums)),
    'hypothetical_removed_modules': sorted(lost),
    'hypothetical_removed_physical_lines': sum(len(files[n].read_text().splitlines()) for n in lost),
    'remaining_W17_importers': sorted(n for n in new if any(i.startswith('W17') for i in graph[n])),
}
print(json.dumps(result, indent=2))
