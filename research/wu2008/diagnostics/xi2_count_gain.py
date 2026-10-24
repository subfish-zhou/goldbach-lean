"""Floating-point diagnostic of the candidate's continuous low-domain gain.

This evaluates a profile using the certified rational sigma *lower* table.
It is not an interval certificate, not the full ordinary-count coefficient,
and not a proof of the 1.894 threshold. Domain and profiles follow
W01ContinuousProfile, W01ContinuousIntegral, NodeActual and ShrinkGeometry.
"""
import json
from fractions import Fraction
from math import log
from scipy.integrate import quad
from first_feedback_candidate import mass

SIGMA = [float(m / (1 - Fraction(858467, 5000000))) for m in mass]
CANDIDATE = [11133/500000, 21591/1000000, 20159/1000000, 563/31250,
             3939/250000, 6447/500000, 9961/1000000, 3841/500000, 7139/1000000]
OLD = [8039587/500000000, 7748071/500000000, 14133223/1000000000,
       12015063/1000000000, 2111073/200000000, 79677/10000000,
       5286731/1000000000, 129933/40000000, 1412473/500000000]
ALPHA, BETA = 100/1327, 25/206
CELLS = [(1 if k == 0 else (21+k)/10, (22+k)/10) for k in range(9)]


def extended_nodes(vector):
    sigma = sum(x*a for x, a in zip(vector, SIGMA))
    extended = {}
    for i in range(2, 30):
        v = 2+i/10
        if i <= 10:
            extended[i] = vector[i-2]
        else:
            value = sigma * log(4/(v-1))
            for x, (a, b) in zip(vector, CELLS):
                a = max(a, v-2)
                if a < b:
                    value += x * quad(lambda t: log((t+1)/(v-1))/t,
                                      a, b, epsabs=1e-12)[0]
            extended[i] = value
    return extended


def lower_profile(vector):
    extended = extended_nodes(vector)
    intervals = [(1, 2.2, vector[0])] + [
        (2+(i-1)/10, 2+i/10, extended[i]) for i in range(3, 30)]

    def h(s):
        return sum(value*log(b/max(a, s-1)) for a, b, value in intervals
                   if max(a, s-1) < b)
    return h


def gain(vector, tolerance):
    h = lower_profile(vector)

    def fibre(x):
        upper = min(0.25, 0.5-2*ALPHA-x)
        cuts = [0.5-x-ALPHA*(2+i/10) for i in range(1, 22)]
        cuts = [y for y in cuts if BETA < y < upper]
        return quad(lambda y: h((0.5-x-y)/ALPHA)/(x*y*(0.5-x-y)),
                    BETA, upper, points=cuts, epsabs=tolerance, epsrel=tolerance)[0]
    return 4*quad(fibre, ALPHA, BETA, points=[0.25-2*ALPHA],
                  epsabs=tolerance, epsrel=tolerance)[0]


if __name__ == '__main__':
    rows = []
    for tolerance in [1e-8, 1e-10]:
        old, new = gain(OLD, tolerance), gain(CANDIDATE, tolerance)
        rows.append({'quadrature_tolerance': tolerance, 'old_sigma_lower_profile_gain': old,
                     'candidate_sigma_lower_profile_gain': new,
                     'difference_divided_by_four': (new-old)/4})
    print(json.dumps({'kind': 'floating_diagnostic_not_a_Lean_certificate', 'runs': rows}, indent=2))
