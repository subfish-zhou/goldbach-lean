#!/usr/bin/env python3
"""Bind Eighth raw integer ceil payments to the accepted Git table.

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
TABLE_SHA256 = '8b03ce0657cbfd1cf2e4b70305e36bc51cb0463fa655d65345f8fe2078a22578'


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


def check_eighth():
    names = ['WR2IntegerLogHorner.lean', 'WR2IntegerLogUpper.lean',
             'WR2ClassicalEighthRawIntegerData.lean', 'WR2ClassicalEighthRawSums.lean',
             'WR2ClassicalEighthRawPayments.lean', 'WR2ExactRationalLog.lean',
             'WR2ClassicalCumulativeDivision.lean']
    frozen = json.loads((OUT/'preserved-data.json').read_text())
    for module, digest in frozen.items():
        require(sha256((SRC/(module+'.lean')).read_bytes()) == digest,
                f'Frozen shared module changed: {module}')
    sources = {name: (SRC/name).read_text() for name in names}
    helper = sources[names[0]]
    bind(helper, 'commonDen', '334639305')
    L = arithmetic(definition(helper, 'commonDen'), set())({})
    require(L == lcm(*range(1, 24, 2)), 'Odd denominator LCM changed')
    rows = definition(helper, 'homogeneous').splitlines()
    require(len(rows) == 3 and normalize(rows[0]) == 'letP:=p^2'
            and normalize(rows[1]) == 'letQ:=q^2', 'Horner coordinates changed')
    horner = arithmetic(rows[2].strip(), {'P', 'Q'})
    bind(helper, 'numerator', '2*p*homogeneous p q')
    bind(helper, 'denominator', 'commonDen*q^23')
    upper = sources[names[1]]
    bind(upper, 'hiNumerator', 'numerator p q*(q^2-p^2)+2*commonDen*p^25')
    bind(upper, 'hiDenominator', 'denominator q*(q^2-p^2)')
    bind(sources['WR2ExactRationalLog.lean'], 'logLo',
         '2 * ∑ i ∈ range 12, ((t-1)/(t+1))^(2*i+1)/(2*i+1 : ℚ)')
    # Preserve the actual source remainder. In particular, there is NO /25.
    bind(sources['WR2ExactRationalLog.lean'], 'logHi',
         'logLo t + 2*((t-1)/(t+1))^25/(1-((t-1)/(t+1))^2)')
    bind(sources['WR2ClassicalCumulativeDivision.lean'], 'ceilDiv', '(n+d-1)/d')
    data = sources[names[2]]
    bind(data, 'scale', '1000000000000')
    bind(data, 'gridDenominator', '16306176')
    bind(data, 'gridNumerator', '1228800+1027*(2*i+1)')
    bind(data, 'cayleyP', 'gridDenominator-3*gridNumerator i')
    bind(data, 'cayleyQ', '3*gridDenominator-3*gridNumerator i')
    bind(data, 'rawNumerator', 'scale*gridDenominator^2*IntegerLogUpper.hiNumerator (cayleyP i) (cayleyQ i)')
    bind(data, 'rawDenominator', '''IntegerLogUpper.hiDenominator (cayleyP i) (cayleyQ i)*
         gridNumerator i*(gridDenominator-gridNumerator i)''')
    bind(data, 'paymentNumerator', '''if i < 2048 then
         ClassicalCumulativeDivision.ceilDiv (rawNumerator i) (rawDenominator i) else 0''')
    bind(data, 'numerator', 'EighthIntegerPayment.paymentNumerator')
    bind(data, 'payment', '(numerator i:ℝ)/1000000000000')
    bind(data, 'paymentBlockSum', '∑ j ∈ Finset.range 64, numerator (64*b+j)')
    scale = arithmetic(definition(data, 'scale'), set())({})
    D = arithmetic(definition(data, 'gridDenominator'), set())({})
    grid = arithmetic(definition(data, 'gridNumerator'), {'i'})

    def raw(i):
        S = grid({'i': i})
        require(0 < S and 3*S < D, 'Nat grid subtraction underflow')
        p, q = D-3*S, 3*D-3*S
        require(0 <= p < q, 'Cayley square subtraction underflow')
        difference = q*q-p*p
        numerator = 2*p*horner({'P': p*p, 'Q': q*q})*difference + 2*L*p**25
        denominator = L*q**23*difference
        return scale*D*D*numerator, denominator*S*(D-S)

    def payment(i):
        require(type(i) is int and i >= 0, 'Index must be Nat')
        if i >= 2048:
            return 0
        n, d = raw(i)
        require(d > 0, 'Zero raw denominator')
        return (n+d-1)//d

    old_raw = subprocess.check_output([
        'git', 'show', BASELINE+':research/wu2008/src/WR2ClassicalEighthRawPayments.lean'], cwd=ROOT)
    require(sha256(old_raw) == TABLE_SHA256, 'Accepted Eighth raw table SHA mismatch')
    blocks = {}
    pattern = r'^def paymentBlock(\d+) : ℕ → ℕ\n(.*?)(?=\ndef |\Z)'
    for label, body in re.findall(pattern, old_raw.decode(), re.M | re.S):
        rows = re.findall(r'^  \| (\d+) => (\d+)$', body, re.M)
        require([int(i) for i, _ in rows] == list(range(16)), 'Malformed old Eighth block')
        require(body.strip().endswith('| _ => 0'), 'Changed old Eighth default')
        require(int(label) not in blocks, 'Duplicate old Eighth block')
        blocks[int(label)] = [int(v) for _, v in rows]
    require(set(blocks) == set(range(128)), 'Missing old Eighth blocks')
    old = [v for b in range(128) for v in blocks[b]]
    values = [payment(i) for i in range(2048)]
    require(values == old, 'An Eighth ceil payment differs from the accepted table')
    targets = re.findall(r'theorem raw_sum_block_(\d+)\s*:\s*'
                         r'paymentBlockSum (\d+) = (\d+) :=', sources[names[3]])
    require(len(targets) == 32, 'Expected 32 block targets')
    require([int(a) for a, _, _ in targets] == list(range(32)), 'Block theorem labels changed')
    require([int(b) for _, b, _ in targets] == list(range(32)), 'Block theorem indices changed')
    totals = [sum(values[b:b+64]) for b in range(0, 2048, 64)]
    require(totals == [int(v) for _, _, v in targets], 'Block target mismatch')
    total_targets = re.findall(r'theorem numerator_sum\s*:\s*'
                              r'\(∑ i ∈ range 2048, numerator i\) = (\d+) :=', sources[names[4]])
    require(total_targets == ['5258450040652036'], 'Total statement changed')
    require(sum(values) == 5258450040652036, 'Total target mismatch')
    outside = [2048, 2049, 4096, 10**12]
    require(all(payment(i) == 0 for i in outside), 'Outside-grid default mismatch')
    samples = list(range(16))+[511, 1023, 1535, 2047]
    for i in samples:
        t = Fraction(grid({'i': i}), D)
        z = (1-3*t)/(3-3*t)
        lo = 2*sum(z**(2*j+1)/Fraction(2*j+1) for j in range(12))
        hi = lo+2*z**25/(1-z*z)  # Intentionally no denominator factor 25.
        reference = scale*hi/(t*(1-t))
        n, d = raw(i)
        require(n*reference.denominator == d*reference.numerator, 'Unrounded logHi mismatch')
    return {
        'status': 'PASS', 'validation_scope': 'Numerical preservation only, not full Lean acceptance',
        'baseline_commit': BASELINE, 'baseline_payment_sha256': TABLE_SHA256,
        'current_source_sha256': {name: sha256((SRC/name).read_bytes()) for name in names},
        'frozen_shared_source_sha256': frozen,
        'source_binding': 'Actual Horner/grid arithmetic AST plus normalized binding of all remaining evaluated definitions, ceilDiv and consumer aliases',
        'logHi_remainder': '2*z^25/(1-z^2), without /25',
        'payment_count': 2048, 'all_ceil_payments_equal': True,
        'block_count': 32, 'all_block_targets_equal': True, 'block_sums': totals,
        'total': sum(values), 'first_payment': values[0], 'last_payment': values[-1],
        'outside_zero': {'guard_bound': 2048, 'bound_definition': True, 'samples': outside},
        'unrounded_rational_cross_checks': samples,
        'limitation': 'Python numerical preservation audit; Lean independently certifies the upper-log identity, ceil bound, and each block sum.'}


def main():
    needed = ['WR2IntegerLogUpper.lean', 'WR2ClassicalEighthRawIntegerData.lean',
              'WR2ClassicalEighthRawSums.lean']
    missing = [name for name in needed if not (SRC/name).exists()]
    if missing:
        raise SystemExit('PENDING production Eighth raw sources: '+', '.join(missing))
    report = check_eighth()
    target = OUT/'eighth-values.json'
    target.write_text(json.dumps(report, indent=2, ensure_ascii=False)+'\n')
    print(f'PASS numerical audit: {report["payment_count"]} ceil payments, '
          f'{report["block_count"]} block targets; total {report["total"]}; {target}')


if __name__ == '__main__':
    main()
