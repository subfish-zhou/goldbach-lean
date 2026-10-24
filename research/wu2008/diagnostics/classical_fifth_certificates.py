#!/usr/bin/env python3
"""Reproduce the fifth classical-slot certificates with exact rational arithmetic.

Three 1024-point midpoint grids generate 192 point modules, 192 coverage
modules, three payment tables, three roots and one final assembly. The degree
12 correction polynomial is obtained by integrating two polynomial products.
Neither symbolic-algebra packages nor stored numerical data are required.
Byte reproduction is separate from Lean verification of all dependencies.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse

def correction_coefficients():
    """Coefficients of C(x) = integral_0^x B(t) Q_3(t), B' = logPoly Q_2."""

    def product(p, q):
        out = [F(0)] * (len(p) + len(q) - 1)
        for i, a in enumerate(p):
            for j, b in enumerate(q):
                out[i + j] += a * b
        return out

    def primitive(p):
        return [F(0)] + [c / (i + 1) for i, c in enumerate(p)]
    log_poly = [F(0), F(1), F(-1, 2), F(1, 3), F(-1, 4)]
    q2 = [F((-1) ** j, 2 ** (j + 1)) for j in range(4)]
    q3 = [F((-1) ** j, 3 ** (j + 1)) for j in range(4)]
    return primitive(product(primitive(product(log_poly, q2)), q3))

def point_data():
    """Compute exact grid points and round their lower values down to scale 10^12."""
    R, r, alpha = (F(1327, 200), F(1327, 824), F(100, 1327))
    lo, cut, hi = (R - 2 * r, R - 1 - r, R - 2)
    coefficients = correction_coefficients()
    count, scale = (1024, 10 ** 12)

    def log_lower(x):
        z = (x - 1) / (x + 1)
        return 2 * sum((z ** (2 * j + 1) / (2 * j + 1) for j in range(12)))

    def correction(x):
        value = F(0)
        for coefficient in reversed(coefficients):
            value = value * x + coefficient
        return value
    rows = []
    for tag, left, right in [('initial', lo, F(4)), ('middle', F(4), cut), ('terminal', cut, hi)]:
        step = (right - left) / count
        points = []
        for i in range(count):
            s = left + step * F(2 * i + 1, 2)
            ratio = r / (R - r - s) if tag != 'terminal' else R - 1 - s
            profile = log_lower(s - 1) + (correction(s - 4) if tag != 'initial' else 0)
            value = profile * log_lower(ratio) / (s * (F(1, 2) - alpha * s))
            q = value.numerator * scale // value.denominator
            points.append({'s': str(s), 'ratio': str(ratio), 'q': q})
        rows.append({'tag': tag, 'n': count, 'sum': sum((p['q'] for p in points)), 'points': points})
    return rows

def point_sources(data):
    out = {}

    def lit(v):
        return f'({v.numerator}/{v.denominator}:ℝ)'
    for row in data:
        tag = row['tag']
        cap = tag.capitalize()
        for block in range(64):
            name = f'WR2ClassicalFifth{cap}Points{block:03d}'
            s = """import WR2ClassicalFifthRational
noncomputable section
namespace WuPaper.ClassicalFifthRational
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
"""
            names = []
            for i in range(block * 16, (block + 1) * 16):
                p = row['points'][i]
                x = F(p['s'])
                ratio = F(p['ratio'])
                extra = '0' if tag == 'initial' else f'(ClassicalCPolynomial.cPoly {lit(x - 4)})'
                thm = f'paid_{tag}_{i}'
                names.append(thm)
                s += f'theorem {thm} : ({p['q']}:ℝ)/1000000000000 ≤ value {extra} {lit(ratio)} {lit(x)} := by\n  norm_num [value,WuSource.SrcFourEnclosure.logLo,Finset.sum_range_succ' + (',ClassicalCPolynomial.cPoly' if tag != 'initial' else '') + ']\n\n'
            s += 'end WuPaper.ClassicalFifthRational\n' + ''.join((f'#print axioms WuPaper.ClassicalFifthRational.{n}\n' for n in names))
            out[name + '.lean'] = s
    return out

def payment_sources(data):
    root = {}
    K = 10 ** 12
    for row, start, stop in zip(data, ['lo', '4', 'cut'], ['4', 'cut', 'hi']):
        key = row['tag']
        tag = key.capitalize()
        nums = [p['q'] for p in row['points']]
        s = """import WR2ClassicalFifthAssembly
noncomputable section
namespace WuPaper.ClassicalFifthRational
open Finset
"""
        for b in range(64):
            s += f"""def {key}Block{b:03d} : ℕ → ℕ
"""
            for j in range(16):
                s += f"""  | {j} => {nums[16 * b + j]}
"""
            s += """  | _ => 0
"""
        s += f"""def {key}Numerator (i : ℕ) : ℕ :=
  match i/16 with
"""
        for b in range(64):
            s += f"""  | {b} => {key}Block{b:03d} (i%16)
"""
        s += f"""  | _ => 0
def {key}Payment (i : ℕ) : ℝ := ({key}Numerator i:ℝ)/{K}
"""
        s += f"""set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem {key}_sum : (∑ i ∈ range 1024, {key}Numerator i) = {row['sum']} := by
  decide +kernel

theorem {key}_total : ({row['sum']}:ℝ)/{K} ≤ ∑ i ∈ range 1024, {key}Payment i := by
  simp only [{key}Payment,← Finset.sum_div,← Nat.cast_sum,{key}_sum]
  rfl
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.{key}_total
"""
        root[f'WR2ClassicalFifth{tag}Payments.lean'] = s
        for b in range(64):
            s = f"""import WR2ClassicalFifth{tag}Payments
import WR2ClassicalFifth{tag}Points{b:03d}
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem {key}_grid_block_{b:03d} (j : Fin 16) : {key}Payment (16*{b}+j.val) ≤
    {key}Value ((point {start} {stop} 1024 (16*{b}+j.val)+point {start} {stop} 1024 (16*{b}+j.val+1))/2) := by
  fin_cases j
"""
            for j in range(16):
                i = 16 * b + j
                p = row['points'][i]
                x = F(p['s'])
                ratio = F(p['ratio'])
                lit = f'({x.numerator}:ℝ)/{x.denominator}'
                rr = f'({ratio.numerator}:ℝ)/{ratio.denominator}'
                exp = f'ClassicalSixthBranch.r/ClassicalSixthBranch.v ({lit})' if key != 'terminal' else f'ClassicalSixthBranch.u ({lit})'
                s += f"""  · change {key}Payment {i} ≤ {key}Value ((point {start} {stop} 1024 {i}+point {start} {stop} 1024 {i + 1})/2)
    have hp : {key}Payment {i} = ({nums[i]}:ℝ)/{K} := rfl
    have hx : (point {start} {stop} 1024 {i}+point {start} {stop} 1024 {i + 1})/2 = {lit} := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : {exp} = {rr} := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold {key}Value
    rw [hr]
"""
                if key != 'initial':
                    xx = x - 4
                    s += f"""    rw [show ({lit})-4 = ({xx.numerator}:ℝ)/{xx.denominator} by norm_num]
"""
                s += f"""    exact paid_{key}_{i}
"""
            s += f"""end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.{key}_grid_block_{b:03d}
"""
            root[f'WR2ClassicalFifth{tag}GridBlock{b:03d}.lean'] = s
        s = ''.join((f'import WR2ClassicalFifth{tag}GridBlock{b:03d}\n' for b in range(64)))
        s += f"""noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxHeartbeats 4000000 in
theorem all_{key}_paid (i : ℕ) (hin : i < 1024) : {key}Payment i ≤
    {key}Value ((point {start} {stop} 1024 i+point {start} {stop} 1024 (i+1))/2) := by
  have hj : i%16 < 16 := Nat.mod_lt _ (by norm_num)
  have hb : i/16 < 64 := by omega
  have hh (b : Fin 64) : {key}Payment (16*b.val+i%16) ≤
      {key}Value ((point {start} {stop} 1024 (16*b.val+i%16)+point {start} {stop} 1024 (16*b.val+i%16+1))/2) := by
    fin_cases b
"""
        for b in range(64):
            s += f"""    · exact {key}_grid_block_{b:03d} ⟨i%16,hj⟩
"""
        s += f"""  have he : 16*(i/16)+i%16=i := by omega
  simpa only [he] using hh ⟨i/16,hb⟩
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.all_{key}_paid
"""
        root[f'WR2ClassicalFifth{tag}Root.lean'] = s
    s = """import WR2ClassicalFifthInitialRoot
import WR2ClassicalFifthMiddleRoot
import WR2ClassicalFifthTerminalRoot
noncomputable section
namespace WuPaper.ClassicalFifthRational

theorem fifth_main_lower : (165533:ℝ)/100000 ≤ Wu08TerminalAlignment.fifthMain :=
  ClassicalFifthAssembly.fifth_lower_of_payments initialPayment middlePayment terminalPayment
    all_initial_paid all_middle_paid all_terminal_paid initial_total middle_total terminal_total

end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.fifth_main_lower
"""
    root['WR2ClassicalFifthCertificate.lean'] = s
    return root

def generate():
    data = point_data()
    sources = point_sources(data)
    payments = payment_sources(data)
    assert not sources.keys() & payments.keys()
    sources.update(payments)
    return sources

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--check', type=Path, metavar='DIR', help='Compare generated bytes with DIR without modifying it.')
    mode.add_argument('--write', type=Path, metavar='DIR', help='Write generated Lean sources into DIR.')
    args = parser.parse_args()
    sources = generate()
    if args.check is not None:
        mismatches = [name for name, text in sources.items() if not (args.check / name).is_file() or (args.check / name).read_bytes() != text.encode()]
        if mismatches:
            raise SystemExit('Missing or different generated sources: ' + ', '.join(mismatches))
        print(f'CHECK_PASS {len(sources)} generated modules; Lean verification is separate.')
    else:
        args.write.mkdir(parents=True, exist_ok=True)
        for name, text in sources.items():
            (args.write / name).write_bytes(text.encode())
        print(f'WROTE {len(sources)} generated modules; unverified.')
if __name__ == '__main__':
    main()
