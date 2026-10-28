#!/usr/bin/env python3
"""Bind Fourth Bq integer ceil values to the accepted Git table.

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
TABLE_SHA256 = '9e1a3769d6801c9adf04417d4690f9d734e772f5960db208811929f7e8bac1a4'


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


def check_bq():
    names = ['WR2IntegerLogHorner.lean', 'WR2IntegerLogUpper.lean',
             'WR2ClassicalFourthDataBq.lean', 'WR2ExactRationalLog.lean',
             'WR2ClassicalCumulativeDivision.lean', 'WR2ClassicalFourthTableCheck.lean']
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
    bind(sources[names[1]], 'hiNumerator', 'numerator p q*(q^2-p^2)+2*commonDen*p^25')
    bind(sources[names[1]], 'hiDenominator', 'denominator q*(q^2-p^2)')
    bind(sources['WR2ExactRationalLog.lean'], 'logLo',
         '2 * ∑ i ∈ range 12, ((t-1)/(t+1))^(2*i+1)/(2*i+1 : ℚ)')
    bind(sources['WR2ExactRationalLog.lean'], 'logHi',
         'logLo t + 2*((t-1)/(t+1))^25/(1-((t-1)/(t+1))^2)')
    bind(sources['WR2ClassicalCumulativeDivision.lean'], 'ceilDiv', '(n+d-1)/d')
    bind(sources['WR2ClassicalFourthTableCheck.lean'], 'splitUpper', '''
         (logHi ((1+(t-1))/2) + logHi (2*(t-1)/(1+(t-1))))/t''')
    data = sources[names[2]]
    bind(data, 'BqRawNumerator', '''
        1000000000000000*4000*(hiNumerator i (16000+i)*hiDenominator i (16000+3*i)+
          hiNumerator i (16000+3*i)*hiDenominator i (16000+i))''')
    bind(data, 'BqRawDenominator', '(8000+i)*hiDenominator i (16000+i)*hiDenominator i (16000+3*i)')
    bind(data, 'Bq', '''if i ≤ 10540 then
        ClassicalCumulativeDivision.ceilDiv (BqRawNumerator i) (BqRawDenominator i) else 0''')

    def hi(p, q):
        require(0 <= p < q, 'Cayley square subtraction underflow')
        difference = q*q-p*p
        n = 2*p*horner({'P': p*p, 'Q': q*q})*difference + 2*L*p**25
        return n, L*q**23*difference

    def raw(i):
        a, c = hi(i, 16000+i)
        b, d = hi(i, 16000+3*i)
        return 10**15*4000*(a*d+b*c), (8000+i)*c*d

    def value(i):
        require(type(i) is int and i >= 0, 'Index must be Nat')
        if i > 10540:
            return 0
        n, d = raw(i)
        require(d > 0, 'Zero raw denominator')
        return (n+d-1)//d

    old_raw = subprocess.check_output([
        'git', 'show', BASELINE+':research/wu2008/src/WR2ClassicalFourthDataBq.lean'], cwd=ROOT)
    require(sha256(old_raw) == TABLE_SHA256, 'Accepted Fourth Bq table SHA mismatch')
    blocks = {}
    pattern = r'^def BqBlock(\d+) : ℕ → ℕ\n(.*?)(?=\ndef |\Z)'
    for label, body in re.findall(pattern, old_raw.decode(), re.M | re.S):
        index = int(label)
        rows = re.findall(r'^  \| (\d+) => (\d+)$', body, re.M)
        expected_count = 45 if index == 82 else 128
        require([int(i) for i, _ in rows] == list(range(expected_count)), 'Malformed old Bq block')
        require(body.strip().endswith('| _ => 0'), 'Changed old Bq default')
        require(index not in blocks, 'Duplicate old Bq block')
        blocks[index] = [int(v) for _, v in rows]
    require(set(blocks) == set(range(83)), 'Missing old Bq blocks')
    old = [v for b in range(83) for v in blocks[b]]
    values = [value(i) for i in range(10541)]
    require(values == old, 'A Bq ceil value differs from the accepted table')
    require(value(0) == 0, 'Exact zero endpoint changed')
    outside = [10541, 10623, 10624, 10**12]
    require(all(value(i) == 0 for i in outside), 'Outside-support default mismatch')
    samples = list(range(16))+[2540, 4000, 8000, 10540]
    for i in samples:
        x = Fraction(4000+i, 4000)
        def loghi(t):
            z = (t-1)/(t+1)
            lo = 2*sum(z**(2*j+1)/Fraction(2*j+1) for j in range(12))
            return lo+2*z**25/(1-z*z)  # Preserve source remainder without /25.
        reference = 10**15*(loghi((1+x)/2)+loghi(2*x/(1+x)))/(1+x)
        n, d = raw(i)
        require(n*reference.denominator == d*reference.numerator, 'Unrounded split-upper mismatch')
    exact = [i for i in range(10541) if raw(i)[0] % raw(i)[1] == 0]
    require(exact == [0], 'Exact-division endpoint set changed')
    return {
        'status': 'PASS', 'validation_scope': 'Numerical preservation only, not full Lean acceptance',
        'baseline_commit': BASELINE, 'baseline_payment_sha256': TABLE_SHA256,
        'current_source_sha256': {name: sha256((SRC/name).read_bytes()) for name in names},
        'frozen_shared_source_sha256': frozen,
        'source_binding': 'Actual Horner arithmetic AST plus normalized binding of all remaining evaluated formulas, logHi and ceilDiv',
        'logHi_remainder': '2*z^25/(1-z^2), without /25',
        'payment_count': 10541, 'all_ceil_values_equal': True,
        'first_payment': values[0], 'last_payment': values[-1],
        'exact_division_indices': exact, 'zero_endpoint': True,
        'outside_zero': {'last_supported_index': 10540, 'bound_definition': True, 'samples': outside},
        'unrounded_rational_cross_checks': samples,
        'limitation': 'Python preservation audit; downstream cumulative and final Lean proofs require independent rebuilding.'}


def main():
    data = SRC/'WR2ClassicalFourthDataBq.lean'
    if 'def BqRawNumerator ' not in data.read_text():
        raise SystemExit('PENDING: production Bq remains the accepted literal table; no new PASS written')
    report = check_bq()
    target = OUT/'bq-values.json'
    target.write_text(json.dumps(report, indent=2, ensure_ascii=False)+'\n')
    print(f'PASS numerical audit: {report["payment_count"]} exact ceil values; zero and support preserved; {target}')


if __name__ == '__main__':
    main()
