"""Floating diagnostic of Wu08TerminalAlignment's classical coefficient.

NOT an interval enclosure, Lean certificate, or threshold proof. Method-of-steps
formulas follow Wu08OriginalFirstSteps; integration domains follow
SingleUpperClassicalLimit, FifthPairGeometry, TruncatedSixthLowerGeometry,
SeventhEighthClassicalIntegral, NinthMainMassIntegral, WSrcFourSourceCount,
and U8OriginalSmallIntegral. All H/h and Psi gains are excluded.
"""
import json
import numpy as np
from scipy.integrate import cumulative_trapezoid, quad
from numpy.polynomial.legendre import leggauss

A, B = 100/1327, 25/206
SIGMA, LAM = .5-3*A, .5-2*A


def profiles(step):
    s = np.linspace(0, 8, round(8/step)+1)
    def primitive(values):
        return cumulative_trapezoid(values, s, initial=0)
    k = np.log(np.maximum(1, s-1))/np.maximum(1, s)
    parts = []
    previous = k
    for start in [2, 3, 4, 5]:
        integral = primitive(previous)
        value = np.interp(np.maximum(start, s-1), s, integral)-np.interp(start, s, integral)
        parts.append(value)
        previous = value/np.maximum(1, s)
    upper = 1+parts[0]+parts[2]
    lower = np.log(np.maximum(1, s-1))+parts[1]+parts[3]
    return lambda t: np.interp(t, s, upper), lambda t: np.interp(t, s, lower)


def buchstab(step):
    u = np.linspace(1, 12, round(11/step)+1)
    w = np.zeros_like(u)
    w[u <= 2] = 1/u[u <= 2]
    for n in range(2, 12):
        indices = np.flatnonzero((u >= n) & (u <= n+1))
        v = u[indices]
        derivative = np.interp(v-1, u, w)
        base = n*np.interp(n, u, w)
        w[indices] = (base+cumulative_trapezoid(derivative, v, initial=0))/v
    return lambda t: np.interp(t, u, w)


def four_pair(w, order):
    q, weights = leggauss(order)
    q, weights = (q+1)/2, weights/2
    total = 0
    for left, right, small in [(A, .1, True), (.1, B, False)]:
        x = left+(right-left)*q[:,None,None,None]
        y = x+(B-x)*q[None,:,None,None]
        z = y+(B-y)*q[None,None,:,None]
        t = z+(LAM-2*z)*q[None,None,None,:]
        jac = (right-left)*(B-x)*(B-y)*(LAM-2*z)
        weight = (weights[:,None,None,None]*weights[None,:,None,None]*
                  weights[None,None,:,None]*weights[None,None,None,:])
        kernel = w((1-x-y-z-t)/y)/(x*y*y*z*t)
        total += np.sum(weight*jac*kernel*(7.2/(1-x) if small else 8))
    return float(total)


def evaluate(step, order):
    upper, lower = profiles(step)
    integral = lambda f, a, b: quad(f, a, b, epsabs=2e-9, epsrel=2e-9)[0]
    f1, f2 = 8*lower(.5/A), 8*lower(.5/B)
    single = lambda r: 4*integral(lambda t: upper((.5-t)/A)/(t*(.5-t)), A, r)
    f3, f4 = single(1/3), single(SIGMA)
    f5 = 4*integral(lambda y: integral(
        lambda x: lower((.5-x-y)/A)/(x*y*(.5-x-y)), A, y), A, B)
    f6 = 4*integral(lambda x: integral(
        lambda y: lower((.5-x-y)/A)/(x*y*(.5-x-y)), B, min(SIGMA, LAM-x)), A, B)
    f7 = 8*integral(lambda t: np.log((1-2*t)/t)/(t*(1-t)), SIGMA, 1/3)
    f8raw = 8*integral(lambda t: np.log(2-3*t)/(t*(1-t)), A, 1/3)
    correction = 8*integral(lambda t: np.log(2-3*t)/(t*(1-t))*(1-.9/(1-t)), A, .1)
    f8 = f8raw-correction
    f9 = 8*integral(lambda t: np.log((1-SIGMA-t)/SIGMA)/(t*(1-t)), B, SIGMA)
    pair = four_pair(buchstab(step), order)
    coefficient = (3*f1+f2-f3-f4+f5+f6-2*f7-f8-f9-pair)/4
    return {'profile_step': step, 'gauss_order': order,
            'classical_terms': dict(zip(['first','second','third','fourth','fifth','sixth',
                                         'seventh','eighth','ninth','tenth_plus_eleventh'],
                                        [f1,f2,f3,f4,f5,f6,f7,f8,f9,pair])),
            'classical_coefficient_without_any_H_h_Psi_gain': coefficient,
            'gap_to_4491_over_5000_before_gains': 4491/5000-coefficient}


if __name__ == '__main__':
    print(json.dumps({'kind':'floating_diagnostic_not_a_Lean_certificate',
                      'runs':[evaluate(1/20000,24),evaluate(1/40000,40)]},indent=2))
