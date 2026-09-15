#!/usr/bin/env python3
"""Exact rational enclosure of the fixed Wu08 Table 2 sixth-gain sum.

No floats, optimization, adaptive refinement or external packages.
Usage: python3 sixth_table_gain.py > certificate.json
       python3 sixth_table_gain.py --verify certificate.json
"""
from fractions import Fraction as F
import json, sys

ALPHA, BETA = F(100, 1327), F(25, 206)
VALUES = [211041, 191556, 173631, 157035, 141585, 127132, 113556,
          100756, 88648, 77162, 66236, 55818, 46164, 37529, 30123,
          23901, 18997, 15336, 12593, 10120, 8099]
R0 = (F(1, 2) - 2 * BETA) / ALPHA
R1 = (F(1, 2) - ALPHA - BETA) / ALPHA
SCALE = 2**64
TERMS, SUBDIVISIONS = 12, 32

def floor(x):
    return x.numerator // x.denominator

def ceil(x):
    return -floor(-x)

def pair(x):
    return [x.numerator, x.denominator]

def log_bounds(x):
    assert x >= 1
    t = (x - 1) / (x + 1)
    power, total = t, F(0)
    for j in range(TERMS):
        total += 2 * power / (2*j + 1)
        power *= t*t
    remainder = 2 * power / ((2*TERMS + 1) * (1-t*t))
    return floor(total*SCALE), ceil((total+remainder)*SCALE)

def ratio(s, kind):
    S = F(1, 2) - ALPHA*s
    if kind == 'minus':
        return BETA*(S-ALPHA)/(ALPHA*(S-BETA))
    return (S-ALPHA)*(S-BETA)/(ALPHA*BETA)

def denominator(s):
    return s*(1-2*ALPHA*s)

def cells():
    for i, value in enumerate(VALUES, 1):
        left, right = F(2)+F(i-1, 10), min(F(2)+F(i, 10), R1)
        assert left < right
        cuts = [left] + ([R0] if left < R0 < right else []) + [right]
        for x, y in zip(cuts, cuts[1:]):
            kind = 'minus' if y <= R0 else 'plus'
            for j in range(SUBDIVISIONS):
                a, b = x+(y-x)*F(j, SUBDIVISIONS), x+(y-x)*F(j+1, SUBDIVISIONS)
                yield i, F(value, 10**7), kind, a, b

def geometry(kind, a, b):
    rmin, rmax = sorted([ratio(a, kind), ratio(b, kind)])
    qmin = min(denominator(a), denominator(b))
    vertex = 1/(4*ALPHA)
    qmax = max(denominator(a), denominator(b),
               denominator(vertex) if a <= vertex <= b else F(0))
    assert 1 <= rmin <= rmax and 0 < qmin <= qmax
    return rmin, rmax, qmin, qmax

def produce():
    out, total_lo, total_hi = [], 0, 0
    for i, v, kind, a, b in cells():
        rmin, rmax, qmin, qmax = geometry(kind, a, b)
        llo = log_bounds(rmin)[0]
        lhi = log_bounds(rmax)[1]
        lo = floor(8*v*(b-a)*llo/qmax)
        hi = ceil(8*v*(b-a)*lhi/qmin)
        total_lo += lo
        total_hi += hi
        out.append({'i': i, 'kind': kind, 'a': pair(a), 'b': pair(b),
                    'log_lo': llo, 'log_hi': lhi, 'cell_lo': lo, 'cell_hi': hi})
    assert len(out) == 704
    return {'campaign_id': 'wu08-literal-table2-sixth-gain',
            'alpha': pair(ALPHA), 'beta': pair(BETA), 'values': VALUES,
            'value_denominator': 10**7, 'scale': SCALE, 'log_terms': TERMS,
            'subdivisions': SUBDIVISIONS, 'cells': out,
            'lower': pair(F(total_lo, SCALE)), 'upper': pair(F(total_hi, SCALE)),
            'proves_gain_gt_3_over_50': F(total_lo, SCALE) > F(3, 50)}

def verify(cert):
    assert cert['campaign_id'] == 'wu08-literal-table2-sixth-gain'
    assert cert['alpha'] == pair(ALPHA) and cert['beta'] == pair(BETA)
    assert cert['values'] == VALUES and cert['value_denominator'] == 10**7
    assert cert['scale'] == SCALE and cert['log_terms'] == TERMS
    assert cert['subdivisions'] == SUBDIVISIONS
    expected = list(cells())
    assert len(cert['cells']) == len(expected) == 704
    total_lo, total_hi = 0, 0
    for row, (i, v, kind, a, b) in zip(cert['cells'], expected):
        assert (row['i'], row['kind'], row['a'], row['b']) == (i, kind, pair(a), pair(b))
        rmin, rmax, qmin, qmax = geometry(kind, a, b)
        # Independently check the log certificate via direct powers,
        # not the recurrence used by the producer.
        for x, bound, lower in [(rmin, row['log_lo'], True), (rmax, row['log_hi'], False)]:
            t = (x-1)/(x+1)
            partial = sum((2*t**(2*j+1)/F(2*j+1) for j in range(TERMS)), F(0))
            tail = 2*t**(2*TERMS+1)/(F(2*TERMS+1)*(1-t*t))
            if lower:
                assert F(bound, SCALE) <= partial
            else:
                assert partial+tail <= F(bound, SCALE)
        assert F(row['cell_lo'], SCALE) <= 8*v*(b-a)*F(row['log_lo'], SCALE)/qmax
        assert 8*v*(b-a)*F(row['log_hi'], SCALE)/qmin <= F(row['cell_hi'], SCALE)
        total_lo += row['cell_lo']
        total_hi += row['cell_hi']
    lo, hi = F(total_lo, SCALE), F(total_hi, SCALE)
    assert cert['lower'] == pair(lo) and cert['upper'] == pair(hi)
    assert lo <= hi and lo > F(3, 50)
    assert cert['proves_gain_gt_3_over_50'] is True
    return {'verified': True, 'cells': len(expected), 'lower': pair(lo), 'upper': pair(hi),
            'gain_gt_3_over_50': True}

if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == '--verify':
        print(json.dumps(verify(json.loads(open(sys.argv[2]).read())), indent=2))
    else:
        assert len(sys.argv) == 1
        print(json.dumps(produce(), indent=2))
