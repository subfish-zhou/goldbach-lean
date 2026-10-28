#!/usr/bin/env python3
"""Independently bind integer-payment formulas to the accepted Git tables.

Read-only with respect to Lean sources. Uses only Python's standard library;
never imports a generator, executes Lean, or evaluates source as Python code.
The Horner polynomial is interpreted through a restricted arithmetic AST. Other
Lean definitions must match explicit normalized formulas before evaluation.
This numerical audit supplements, and does not replace, Lean soundness checks.
"""
from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path
import re
import subprocess
from fractions import Fraction
from math import lcm

ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / 'research/wu2008/src'
OUT = Path(__file__).resolve().parent
BASELINE = 'c4e1b8d00dda9661140f95e0f03f0d5a08d636c2'
C_TABLE_SHA256 = '289a63130201118189360a18610bb8f00a833bfafc202fcf480ff13087a29b83'


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def normalize(text: str) -> str:
    return re.sub(r'\s+', '', text)


def definition(text: str, name: str) -> str:
    pattern = (r'^(?:noncomputable )?(?:def|abbrev) ' + re.escape(name)
               + r'\b[^\n]*?:=(.*?)(?=\n\s*\n|\n(?:noncomputable )?'
                 r'(?:def|abbrev) |\nend |\Z)')
    matches = re.findall(pattern, text, re.M | re.S)
    require(len(matches) == 1, f'Expected exactly one definition: {name}')
    return matches[0].strip()


def bind(text: str, name: str, expected: str) -> None:
    require(normalize(definition(text, name)) == normalize(expected),
            f'Lean formula changed: {name}')


def arithmetic(expression: str, variables: set[str]):
    """Parse only names, integer literals, addition, multiplication and powers."""
    tree = ast.parse(expression.replace('^', '**'), mode='eval').body

    def validate(node):
        if isinstance(node, ast.Constant):
            require(type(node.value) is int and node.value >= 0, 'Invalid literal')
        elif isinstance(node, ast.Name):
            require(node.id in variables, f'Unexpected arithmetic name: {node.id}')
        elif isinstance(node, ast.BinOp):
            require(type(node.op) in (ast.Add, ast.Mult, ast.Pow), 'Unexpected operator')
            validate(node.left)
            validate(node.right)
            if isinstance(node.op, ast.Pow):
                require(isinstance(node.right, ast.Constant)
                        and 0 <= node.right.value <= 23, 'Unbounded exponent')
        else:
            raise ValueError(f'Unexpected arithmetic node: {type(node).__name__}')

    validate(tree)

    def evaluate(environment):
        def go(node):
            if isinstance(node, ast.Constant):
                return node.value
            if isinstance(node, ast.Name):
                return environment[node.id]
            a, b = go(node.left), go(node.right)
            if isinstance(node.op, ast.Add):
                return a + b
            if isinstance(node.op, ast.Mult):
                return a * b
            return a ** b
        return go(tree)

    return evaluate


def read_c_table():
    name = 'research/wu2008/src/WR2ClassicalCPayments.lean'
    raw = subprocess.check_output(['git', 'show', f'{BASELINE}:{name}'], cwd=ROOT)
    require(sha256(raw) == C_TABLE_SHA256, 'Accepted C table SHA mismatch')
    blocks = {}
    pattern = r'^def cPaymentBlock(\d+) : ℕ → ℕ\n(.*?)(?=\n\n|\Z)'
    for label, body in re.findall(pattern, raw.decode(), re.M | re.S):
        rows = re.findall(r'^  \| (\d+) => (\d+)$', body, re.M)
        require([int(i) for i, _ in rows] == list(range(16)), 'Malformed old block')
        require(body.strip().endswith('| _ => 0'), 'Changed old default')
        require(int(label) not in blocks, 'Duplicate old block')
        blocks[int(label)] = [int(v) for _, v in rows]
    require(set(blocks) == set(range(256)), 'Missing old blocks')
    return [v for b in range(256) for v in blocks[b]]


def check_c():
    names = ['WR2IntegerLogHorner.lean', 'WR2ClassicalCIntegerData.lean',
             'WR2ClassicalCSums.lean', 'WR2ClassicalCPayments.lean',
             'WR2ExactRationalLog.lean']
    sources = {name: (SRC / name).read_text() for name in names}
    helper = sources[names[0]]
    bind(helper, 'commonDen', '334639305')
    common_den = arithmetic(definition(helper, 'commonDen'), set())({})
    require(common_den == lcm(*range(1, 24, 2)), 'Odd denominator LCM changed')
    polynomial = definition(helper, 'homogeneous').splitlines()
    require(len(polynomial) == 3, 'Unexpected Horner definition shape')
    require(normalize(polynomial[0]) == 'letP:=p^2', 'Horner P changed')
    require(normalize(polynomial[1]) == 'letQ:=q^2', 'Horner Q changed')
    horner = arithmetic(polynomial[2].strip(), {'P', 'Q'})
    bind(helper, 'numerator', '2*p*homogeneous p q')
    bind(helper, 'denominator', 'commonDen*q^23')
    bind(helper, 'splitNumerator', '''numerator (n-d) (n+3*d)*(3*n+d)^23+
        numerator (n-d) (3*n+d)*(n+3*d)^23''')
    bind(helper, 'splitDenominator', 'commonDen*(n+3*d)^23*(3*n+d)^23')
    bind(sources['WR2ExactRationalLog.lean'], 'logLo',
         '2 * ∑ i ∈ range 12, ((t-1)/(t+1))^(2*i+1)/(2*i+1 : ℚ)')

    data = sources[names[1]]
    bind(data, 'scale', '1000000000000')
    bind(data, 'gridDenominator', '1638400')
    bind(data, 'gridNumerator', '3276800+527*(2*i+1)')
    scale = arithmetic(definition(data, 'scale'), set())({})
    denominator = arithmetic(definition(data, 'gridDenominator'), set())({})
    grid = arithmetic(definition(data, 'gridNumerator'), {'i'})
    bind(data, 'rawNumerator', '''scale*gridDenominator*
        splitNumerator (gridNumerator i-gridDenominator) gridDenominator*
        splitNumerator (1127*gridDenominator) (200*(gridNumerator i+gridDenominator))''')
    bind(data, 'rawDenominator', '''gridNumerator i*
        splitDenominator (gridNumerator i-gridDenominator) gridDenominator*
        splitDenominator (1127*gridDenominator) (200*(gridNumerator i+gridDenominator))''')
    bind(data, 'paymentNumerator', 'if i < 4096 then rawNumerator i/rawDenominator i else 0')
    bind(data, 'cPaymentNumerator', 'CIntegerPayment.paymentNumerator')
    bind(data, 'cPayment', '(cPaymentNumerator i:ℝ)/1000000000000')
    bind(data, 'cPaymentBlockSum', '∑ j ∈ Finset.range 64, cPaymentNumerator (64*b+j)')

    def numerator(p, q):
        require(0 <= p < q, 'Unexpected log coordinates')
        return 2 * p * horner({'P': p*p, 'Q': q*q})

    def split(n, d):
        require(n >= d > 0, 'Nat subtraction would truncate')
        p, q, r = n-d, n+3*d, 3*n+d
        return numerator(p, q)*r**23 + numerator(p, r)*q**23, common_den*q**23*r**23

    def raw(i):
        s, d = grid({'i': i}), denominator
        a, c = split(s-d, d)
        b, e = split(1127*d, 200*(s+d))
        return scale*d*a*b, s*c*e

    def payment(i):
        require(type(i) is int and i >= 0, 'Index must be Nat')
        if i >= 4096:
            return 0
        a, b = raw(i)
        require(b > 0, 'Zero payment denominator')
        return a // b

    old = read_c_table()
    values = [payment(i) for i in range(4096)]
    require(values == old, 'A C payment differs from the accepted table')
    block_matches = re.findall(r'theorem c_sum_block_(\d+)\s*:\s*'
                              r'cPaymentBlockSum (\d+) = (\d+) :=', sources[names[2]])
    require(len(block_matches) == 64, 'Expected 64 independently stated sum targets')
    require([int(a) for a, _, _ in block_matches] == list(range(64)), 'Block theorem labels changed')
    require([int(b) for _, b, _ in block_matches] == list(range(64)), 'Block theorem indices changed')
    totals = [sum(values[b:b+64]) for b in range(0, 4096, 64)]
    require(totals == [int(v) for _, _, v in block_matches], 'Block target mismatch')
    total_matches = re.findall(r'theorem cPayment_sum\s*:\s*'
                              r'\(∑ i ∈ range 4096, cPaymentNumerator i\) = (\d+) :=', sources[names[3]])
    require(total_matches == ['207693136875355'], 'Total statement changed')
    require(sum(values) == int(total_matches[0]), 'Total target mismatch')

    # A separate Fraction implementation checks the unrounded finite-log identity.
    def loglo(t):
        z = (t-1)/(t+1)
        return 2*sum(z**(2*j+1)/Fraction(2*j+1) for j in range(12))

    def logs(t):
        return loglo((1+t)/2) + loglo(2*t/(1+t))

    samples = list(range(16)) + [1023, 2047, 3071, 4095]
    for i in samples:
        u = Fraction(grid({'i': i}), denominator)
        reference = scale*logs(u-1)/u*logs(Fraction(1127, 200)/(u+1))
        a, b = raw(i)
        require(a*reference.denominator == b*reference.numerator, 'Unrounded log formula mismatch')
    outside = [4096, 4097, 8192, 10**12]
    require(all(payment(i) == 0 for i in outside), 'Outside-grid default mismatch')
    return {
        'status': 'PASS', 'baseline_commit': BASELINE,
        'baseline_payment_sha256': C_TABLE_SHA256,
        'current_source_sha256': {name: sha256((SRC/name).read_bytes()) for name in names},
        'source_binding': 'Restricted AST interpretation of actual Horner/grid definitions; explicit normalized binding of all other evaluated definitions',
        'entry_count': len(values), 'all_entries_equal': True,
        'block_count': len(totals), 'all_block_targets_equal': True,
        'block_sums': totals, 'total': sum(values),
        'first_payment': values[0], 'last_payment': values[-1],
        'outside_zero': {'guard_bound': 4096, 'bound_definition': True, 'samples': outside},
        'unrounded_rational_cross_checks': samples,
        'limitation': 'Python numerical preservation audit; Lean independently certifies formula soundness and each block sum.'}


def main():
    report = check_c()
    target = OUT / 'c-values.json'
    target.write_text(json.dumps(report, indent=2, ensure_ascii=False) + '\n')
    print(f'PASS C: {report["entry_count"]} entries, {report["block_count"]} block targets, '
          f'total {report["total"]}; {target}')


if __name__ == '__main__':
    main()
