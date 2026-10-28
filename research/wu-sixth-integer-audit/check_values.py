#!/usr/bin/env python3
"""Independently audit Sixth integer payments against fixed Git tables.

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


def sixth_values(data, helper):
    bind(helper, 'commonDen', '334639305')
    L = arithmetic(definition(helper, 'commonDen'), set())({})
    rows = definition(helper, 'homogeneous').splitlines()
    require(len(rows) == 3 and normalize(rows[0]) == 'letP:=p^2'
            and normalize(rows[1]) == 'letQ:=q^2', 'Horner coordinates changed')
    horner = arithmetic(rows[2].strip(), {'P', 'Q'})
    bind(helper, 'numerator', '2*p*homogeneous p q')
    bind(helper, 'denominator', 'commonDen*q^23')
    bind(data, 'scale', '1000000000000')
    bind(data, 'gridDenominator', '168755200')
    bind(data, 'gridNumerator', 'if upper then 576151552+12575*(2*i+1) else 337510400+29131*(2*i+1)')
    bind(data, 'uNumerator', '1127*gridDenominator-200*gridNumerator upper i')
    bind(data, 'vNumerator', '828048*gridDenominator-164800*gridNumerator upper i')
    bind(data, 'weightNumerator', '1327*gridDenominator-200*gridNumerator upper i')
    bind(data, 'ratioNumerator', 'if upper then uNumerator upper i*vNumerator upper i else 1327*uNumerator upper i')
    bind(data, 'ratioDenominator', 'if upper then 53080000*gridDenominator^2 else vNumerator upper i')
    bind(data, 'rawNumerator', '''scale*1327*gridDenominator^2*
        numerator (ratioNumerator upper i-ratioDenominator upper i)
          (ratioNumerator upper i+ratioDenominator upper i)*
        numerator (gridNumerator upper i-2*gridDenominator) (gridNumerator upper i)''')
    bind(data, 'rawDenominator', '''denominator (ratioNumerator upper i+ratioDenominator upper i)*
        denominator (gridNumerator upper i)*gridNumerator upper i*weightNumerator upper i''')
    bind(data, 'paymentNumerator', 'if i < 4096 then rawNumerator upper i/rawDenominator upper i else 0')
    scale = arithmetic(definition(data, 'scale'), set())({})
    D = arithmetic(definition(data, 'gridDenominator'), set())({})
    branches = definition(data, 'gridNumerator').removeprefix('if upper then ').split(' else ')
    require(len(branches) == 2, 'Unexpected Bool grid branches')
    grids = {True: arithmetic(branches[0], {'i'}), False: arithmetic(branches[1], {'i'})}

    def raw(upper, i):
        S = grids[upper]({'i': i})
        u, v, w = 1127*D-200*S, 828048*D-164800*S, 1327*D-200*S
        require(u > 0 and v > 0 and w > 0 and S >= 2*D, 'Nat subtraction underflow')
        n, d = (u*v, 53080000*D*D) if upper else (1327*u, v)
        require(n >= d > 0, 'Ratio Nat subtraction underflow')
        def log_num(p, q):
            return 2*p*horner({'P': p*p, 'Q': q*q})
        numerator = scale*1327*D*D*log_num(n-d, n+d)*log_num(S-2*D, S)
        denominator = L*L*(n+d)**23*S**23*S*w
        return numerator, denominator

    def payment(upper, i):
        require(type(i) is int and i >= 0, 'Index must be Nat')
        if i >= 4096:
            return 0
        n, d = raw(upper, i)
        return n//d

    def loglo(t):
        z = (t-1)/(t+1)
        return 2*sum(z**(2*j+1)/Fraction(2*j+1) for j in range(12))
    samples = list(range(16)) + [1023, 2047, 3071, 4095]
    for upper in [False, True]:
        for i in samples:
            s = Fraction(grids[upper]({'i': i}), D)
            R, r, alpha = Fraction(1327, 200), Fraction(1327, 824), Fraction(100, 1327)
            u, v = R-1-s, R-r-s
            ratio = u*v/r if upper else r*u/v
            reference = scale*loglo(ratio)*loglo(s-1)/(s*(1-2*alpha*s))
            n, d = raw(upper, i)
            require(n*reference.denominator == d*reference.numerator, 'Sixth unrounded mismatch')
        require(all(payment(upper, i) == 0 for i in [4096, 4097, 8192, 10**12]), 'Sixth default changed')
    return {tag: [payment(upper, i) for i in range(4096)]
            for tag, upper in [('lower', False), ('upper', True)]}


def check_sixth():
    frozen = json.loads((OUT/'preserved-data.json').read_text())['WR2IntegerLogHorner']
    require(sha256((SRC/'WR2IntegerLogHorner.lean').read_bytes()) == frozen,
            'Shared Horner changed from the accepted C baseline')
    data_name = 'WR2ClassicalSixthIntegerData.lean'
    names = ['WR2IntegerLogHorner.lean', data_name]
    for tag in ['Lower', 'Upper']:
        names += [f'WR2ClassicalSixth{tag}Sums.lean', f'WR2ClassicalSixth{tag}Payments.lean']
    sources = {name: (SRC/name).read_text() for name in names}
    data = sources[data_name]
    values = sixth_values(data, sources['WR2IntegerLogHorner.lean'])
    specs = [('lower', 'false', '48ac8ecc2ec501af2b0e9c1a26aa29928e99530d25084a21840e4d1263194550', 939922834048256),
             ('upper', 'true', 'e9eef1c99f95cf61a565bb7802f9669f2ea2ac8d156ec4dc2101bb871ac3d772', 1025832247091325)]
    families = {}
    for tag, flag, old_sha, expected_total in specs:
        bind(data, tag+'Numerator', f'SixthIntegerPayment.paymentNumerator {flag}')
        bind(data, tag+'Payment', f'({tag}Numerator i:ℝ)/1000000000000')
        bind(data, tag+'PaymentBlockSum', f'∑ j ∈ Finset.range 64, {tag}Numerator (64*b+j)')
        module = f'WR2ClassicalSixth{tag.title()}Payments.lean'
        raw = subprocess.check_output(['git', 'show', BASELINE+':research/wu2008/src/'+module], cwd=ROOT)
        require(sha256(raw) == old_sha, f'Accepted {tag} table SHA mismatch')
        blocks = {}
        pattern = r'^def '+tag+r'Block(\d+) : ℕ → ℕ\n(.*?)(?=\ndef |\Z)'
        for label, body in re.findall(pattern, raw.decode(), re.M | re.S):
            rows = re.findall(r'^  \| (\d+) => (\d+)$', body, re.M)
            require([int(i) for i, _ in rows] == list(range(16)), f'Malformed old {tag} block')
            require(body.strip().endswith('| _ => 0'), f'Changed old {tag} default')
            require(int(label) not in blocks, f'Duplicate old {tag} block')
            blocks[int(label)] = [int(v) for _, v in rows]
        require(set(blocks) == set(range(256)), f'Missing old {tag} blocks')
        old = [v for b in range(256) for v in blocks[b]]
        require(values[tag] == old, f'A {tag} payment differs from the accepted table')
        sums_name = f'WR2ClassicalSixth{tag.title()}Sums.lean'
        targets = re.findall(r'theorem '+tag+r'_sum_block_(\d+)\s*:\s*'
                             +tag+r'PaymentBlockSum (\d+) = (\d+) :=', sources[sums_name])
        require(len(targets) == 64, f'Expected 64 {tag} block targets')
        require([int(a) for a, _, _ in targets] == list(range(64)), f'{tag} labels changed')
        require([int(b) for _, b, _ in targets] == list(range(64)), f'{tag} block indices changed')
        totals = [sum(values[tag][b:b+64]) for b in range(0, 4096, 64)]
        require(totals == [int(v) for _, _, v in targets], f'{tag} block target mismatch')
        total_targets = re.findall(r'theorem '+tag+r'_sum\s*:\s*'
                                  r'\(∑ i ∈ range 4096, '+tag+r'Numerator i\) = (\d+) :=', sources[module])
        require(total_targets == [str(expected_total)], f'{tag} total statement changed')
        require(sum(values[tag]) == expected_total, f'{tag} total mismatch')
        families[tag] = {'baseline_payment_sha256': old_sha, 'entry_count': 4096,
                         'all_entries_equal': True, 'block_count': 64,
                         'all_block_targets_equal': True, 'block_sums': totals,
                         'total': expected_total, 'first_payment': values[tag][0],
                         'last_payment': values[tag][-1]}
    return {'status': 'PASS', 'validation_scope': 'Numerical preservation only, not full Lean acceptance',
            'payment_count': 8192, 'block_count': 128,
            'shared_horner_unchanged_sha256': frozen, 'baseline_commit': BASELINE,
            'current_source_sha256': {name: sha256((SRC/name).read_bytes()) for name in names},
            'source_binding': 'Actual Horner/grid arithmetic AST plus normalized binding of all other evaluated formulas and consumer aliases',
            'families': families,
            'outside_zero': {'guard_bound': 4096, 'bound_definition': True, 'samples': [4096, 4097, 8192, 10**12]},
            'unrounded_rational_cross_checks_per_family': list(range(16))+[1023, 2047, 3071, 4095],
            'limitation': 'Python numerical preservation audit; Lean independently certifies formula soundness and each block sum.'}



def main():
    needed = ['WR2ClassicalSixthIntegerData.lean', 'WR2ClassicalSixthLowerSums.lean',
              'WR2ClassicalSixthUpperSums.lean']
    missing = [name for name in needed if not (SRC/name).exists()]
    if missing:
        raise SystemExit('PENDING production Sixth sources: '+', '.join(missing))
    report = check_sixth()
    target = OUT/'sixth-values.json'
    target.write_text(json.dumps(report, indent=2, ensure_ascii=False)+'\n')
    print(f'PASS numerical audit: {report["payment_count"]} payments, '
          f'{report["block_count"]} block targets; unchanged shared Horner; {target}')


if __name__ == '__main__':
    main()
