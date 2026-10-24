"""Floating diagnostics for original H/h source gains, NOT Lean bounds.

Uses the rational sigma lower table, rather than evaluating the true sigma.
The comparison is against the old rational vector, not the stronger W17 vector.
These source terms cannot simply be added to an existing count coefficient.
Formulas: NodeGrid, WSrcSingleLogWeights, WSrcSingleOriginalLedger,
WSrcFifthGainCells, and WSrcFifthGainWeight.
"""
import json
from math import log
from scipy.integrate import quad
from xi2_count_gain import ALPHA, BETA, OLD, CANDIDATE, extended_nodes


def source_gains(vector, tolerance):
    upper = extended_nodes(vector)
    node = lambda i: 2+i/10

    def lower(j):
        return vector[0]*log(node(max(2, j-10))/(node(j)-1)) + sum(
            upper[i]*log(node(i)/node(i-1)) for i in range(max(3, j-9), 30))

    second = 8*(lower(22)+upper[12]*log(40/39))
    grid = [1327/400] + [(33+k)/10 for k in range(1, 17)]
    fourth = 8*sum(log(b*(1-2*ALPHA*a)/(a*(1-2*ALPHA*b)))*upper[14+k]
                   for k, (a, b) in enumerate(zip(grid, grid[1:])))
    s0, q = (0.5-2*BETA)/ALPHA, (0.5-2*ALPHA)/ALPHA
    split = (0.5-ALPHA-BETA)/ALPHA

    def weight(s):
        numerator = (log(2*BETA/(1-2*BETA-2*ALPHA*s)) if s <= split
                     else log(1/(2*ALPHA)-1-s))
        return numerator/(s*(1-2*ALPHA*s))

    fifth = 0
    for j in range(13):
        a, b = max(s0, node(14+j)), min(q, node(15+j))
        cuts = [split] if a < split < b else []
        fifth += 8*lower(15+j)*quad(weight, a, b, points=cuts,
                                  epsabs=tolerance, epsrel=tolerance)[0]
    return {'second_node_gain': second, 'fourth_node_sum': fourth,
            'single_source_gain': second+2*fourth, 'fifth_grid_gain': fifth}


if __name__ == '__main__':
    runs = []
    for tolerance in [1e-8, 1e-10]:
        old, new = source_gains(OLD, tolerance), source_gains(CANDIDATE, tolerance)
        runs.append({'tolerance': tolerance, 'old_rational_vector': old,
                     'candidate': new, 'difference': {k: new[k]-old[k] for k in old}})
    print(json.dumps({'kind': 'floating_diagnostic_not_a_Lean_certificate',
                      'runs': runs}, indent=2))
