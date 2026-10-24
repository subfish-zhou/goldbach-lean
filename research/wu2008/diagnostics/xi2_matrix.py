"""Numerical diagnostics only: no output of this script is a Lean certificate.

Integrate the literal kernels in WR2XiFirstKernel/SecondDefinitions, splitting
at every indicator endpoint. Compare the nine-cell fixed point with the table
both before and after the proved Gamma5 debit.
"""
import json
from math import log, floor
from fractions import Fraction
from functools import lru_cache

import numpy as np
from scipy.integrate import quad

ROWS = [(2.2, 4.54, 3.53, 2.90, 2.44), (2.3, 4.50, 3.54, 2.88, 2.43),
        (2.4, 4.46, 3.57, 2.87, 2.40), (2.5, 4.12, 3.56, 2.91, 2.50)]
FIRST = [(2.6, 3.58), (2.7, 3.47), (2.8, 3.34), (2.9, 3.19), (3., 3.)]
EDGES = [1.] + [2.2 + k/10 for k in range(9)]
BASE = np.array([.015826357, .015247971, .013898757, .011776059,
                 .009405211, .006558950, .003536751, .001056651, 0.])
DEBIT = np.array([1/1500, 1/1000, 9/8000, 1/2000] + [0.]*5)
TARGET = np.array([.0223939, .0217196, .0202876, .0181433, .0158644,
                   .0129923, .0100686, .0078162, .0072943])


def integrate(f, a, b):
    return quad(f, a, b, epsabs=2e-12, epsrel=2e-11)[0]


D0 = integrate(lambda v: log(4/(v-1))/v, 3, 5)


@lru_cache(maxsize=32768)
def sigma0(t):
    return integrate(lambda v: log((t+1)/(v-1))/v, 3, t+2)/(1-D0)


def alphas(p):
    s, S, k1, k2, k3 = p
    return [k1-2, S-2, S-S/s-1, S-S/k2-1, S-S/k3-1,
            S-2*S/k2, S-S/k1-S/k3, S-S/k1-S/k2, k1-k1/k2-1]


def xi2(p, t):
    s, S, k1, k2, k3 = p
    a1,a2,a3,a4,a5,a6,a7,a8,a9 = alphas(p)
    product = (s-1)*(S-1)*(k1-1)*(k2-1)*(k3-1)
    # Evaluate logarithms only on their indicator support.
    parts = [(a2,3,lambda: log((t+1)**5/product)/(5*t)),
             (a9,a1,lambda: log((t+1)/((k2-1)*(k1-1-t)))/(5*t)),
             (a5,a2,lambda: log((t+1)/((k3-1)*(S-1-t)))/(5*t)),
             (a3,a2,lambda: log((t+1)/((s-1)*(S-1-t)))/(5*t)),
             (a1,a2,lambda: log((t+1)**2/((k1-1)*(k2-1)))/(5*t)),
             (a7,a5,lambda: log(S*S/((k1*S-S-k1*t)*(k3*S-S-k3*t)))/(5*t*(1-t/S))),
             (a5,a8,lambda: log(S*(S-1-t)/(k1*S-S-k1*t))/(5*t*(1-t/S))),
             (a6,a8,lambda: log(S/(k2*S-S-k2*t))/(5*t*(1-t/S))),
             (a8,a2,lambda: log(S-1-t)/(5*t*(1-t/S)))]
    return sigma0(t)*log(1024/product)/(5*t) + sum(f() for a,b,f in parts if a <= t <= b)


def xi1(p, t):
    s,S = p
    value = sigma0(t)*log(16/((s-1)*(S-1)))/(2*t)
    if S-2 <= t <= 3:
        value += log((t+1)**2/((s-1)*(S-1)))/(2*t)
    if S-S/s-1 <= t <= S-2:
        value += log((t+1)/((s-1)*(S-1-t)))/(2*t)
    return value


def cell(f, a, b, breaks):
    points = sorted(set([a,b] + [v for v in breaks if a < v < b]))
    return sum(integrate(f, x, y) for x,y in zip(points,points[1:]))


def original_feedback(p, z):
    """Independent original J/66/67/68 integrals for a nine-cell profile."""
    s,S,k1,k2,k3 = p
    cells = list(zip(EDGES,EDGES[1:],z))
    a = sum(v*integrate(lambda t: sigma0(t)/t, lo,hi) for lo,hi,v in cells)

    def profile(t):
        return sum(v for lo,hi,v in cells if lo < t <= hi)

    def g(u):
        return a + sum(v*log(hi/max(lo,u-1)) for lo,hi,v in cells if u-1 < hi)

    def e(v):
        return a*log(4/(v-1)) + sum(w*integrate(lambda t: log((t+1)/(v-1))/t,
                   max(lo,v-2),hi) for lo,hi,w in cells if v-2 < hi)

    def J(r):
        return cell(lambda u: g(S*u)/(u*(1-u)), 1-1/r,1-1/S,
                    [(t+1)/S for t in EDGES])

    def inner(x, lo, hi, scale):
        return cell(lambda u: profile(scale*(1-x-u))/(u*(1-x-u)),
                    lo,hi,[1-x-t/scale for t in EDGES])

    # Outer breakpoints where a moving inner cell boundary meets an endpoint.
    b66 = [1-1/k2-t/S for t in EDGES] + [(1-t/S)/2 for t in EDGES]
    v66 = cell(lambda x: inner(x,x,1/k2,S)/x,1/S,1/k2,b66)
    b67 = [1-1/k-t/S for k in [k2,k3] for t in EDGES]
    v67 = cell(lambda x: inner(x,1/k2,1/k3,S)/x,1/S,1/k1,b67)
    b68 = [(1-1/k2)/(t+1) for t in EDGES] + [1/(t+2) for t in EDGES]
    v68 = cell(lambda x: inner(x,x,1/k2,1/x)/x,1/S,1/k1,b68)
    return (J(s)+J(k2)+J(k3)+4*e(S)+e(k1)+v66+v67+v68)/5


def excluded_gamma5_mass(p):
    """Raw missing triangle mass divided by five; all its samples lie in cell zero."""
    _,S,_,k2,_ = p
    B = 1/k2

    def inner(x):
        lo = max(x,1-2*x)
        if lo >= B:
            return 0.
        return integrate(lambda u: 1/(x*u*(1-x-u)),lo,B)

    return cell(inner,1/S,B,[(1-B)/2,1/3])/5


def rational_candidate(matrix):
    """Propose rational data; analytic entry bounds still require Lean proofs."""
    M = [[Fraction(floor(v*1000),1000) for v in row] for row in matrix]
    b = [Fraction(n,10**9) for n in [15826357,15247971,13898757,11776059,
                                    9405211,6558950,3536751,1056651,0]]
    z = [Fraction(0)]*9
    for _ in range(16):
        z = [Fraction(floor((b[i]+sum(M[i][k]*z[k] for k in range(9)))*10**6),10**6)
             for i in range(9)]
    residual = [b[i]+sum(M[i][k]*z[k] for k in range(9))-z[i] for i in range(9)]
    return {'matrix': [[str(v) for v in row] for row in M],
            'vector': list(map(str,z)), 'exact_arithmetic_residual': list(map(str,residual)),
            'analytic_entry_bounds_proved': False, 'sufficient_for_1894_proved': False}


def main():
    matrix = np.array([[cell(lambda t: xi2(p,t), a,b,alphas(p)) for a,b in zip(EDGES,EDGES[1:])]
                       for p in ROWS] +
                      [[cell(lambda t: xi1(p,t), a,b,[p[1]-2,p[1]-p[1]/p[0]-1])
                        for a,b in zip(EDGES,EDGES[1:])] for p in FIRST])
    legal = matrix.copy()
    excluded = np.array([excluded_gamma5_mass(p) for p in ROWS])
    legal[:4,0] -= excluded
    report = {'kind': 'floating-point diagnostic; NOT a proof or certificate',
              'D0': D0, 'matrix': matrix.tolist(),
              'rational_candidate': rational_candidate(legal),
              'excluded_gamma5_column_zero': excluded.tolist(),
              'legal_matrix_fixed_point': np.linalg.solve(np.eye(9)-legal,BASE).tolist(),
              'legal_target_residual': (BASE+legal@TARGET-TARGET).tolist(),
              'spectral_radius': float(max(abs(np.linalg.eigvals(matrix)))),
              'original_integral_crosscheck_error': [original_feedback(p,TARGET)-matrix[i]@TARGET
                                                    for i,p in enumerate(ROWS)],
              'target_residual_without_gamma5_debit': (BASE+matrix@TARGET-TARGET).tolist(),
              'target_residual_with_gamma5_debit': (BASE-DEBIT+matrix@TARGET-TARGET).tolist(),
              'fixed_point_without_gamma5_debit': np.linalg.solve(np.eye(9)-matrix,BASE).tolist(),
              'fixed_point_with_gamma5_debit': np.linalg.solve(np.eye(9)-matrix,BASE-DEBIT).tolist()}
    print(json.dumps(report,indent=2))


if __name__ == '__main__':
    main()
