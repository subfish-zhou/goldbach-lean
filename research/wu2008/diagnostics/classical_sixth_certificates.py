#!/usr/bin/env python3
"""Reproduce the sixth classical-slot midpoint certificates using exact rationals.

Outputs 8192 point inequalities in 512 modules, their payment tables and
coverage proofs, and the final assembly. Generation and byte comparison do
not certify the inequalities: Lean must check every generated module and its
analytic dependencies. No floating-point calculations are used.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse

def point_sources():
    """Round each of the two 4096-point midpoint grids down to scale 10^12."""
    out = {}
    a = F(100, 1327)
    b = F(25, 206)
    cut = (F(1, 2) - 2 * b) / a
    end = (F(1, 2) - a - b) / a
    N = 4096
    K = 10 ** 12

    def lo(r):
        z = (r - 1) / (r + 1)
        return 2 * sum((z ** (2 * j + 1) / F(2 * j + 1) for j in range(12)))

    def lit(v):
        return f'({v.numerator}/{v.denominator}:ℝ)'
    data = {}
    for tag, start, stop in [('Lower', F(2), cut), ('Upper', cut, end)]:
        h = (stop - start) / N
        points = []
        for i in range(N):
            s = start + h * F(2 * i + 1, 2)
            z = F(1, 2) - a * s
            u = min(b, z - b)
            ratio = u * (z - a) / (a * (z - u))
            v = lo(ratio) * lo(s - 1) / (s * (1 - 2 * a * s))
            q = v.numerator * K // v.denominator
            points.append({'s': str(s), 'ratio': str(ratio), 'q': q})
        for block in range(N // 16):
            name = f'WR2ClassicalSixth{tag}Points{block:03d}'
            text = """import WR2ClassicalSixthRational
noncomputable section
namespace WuPaper.ClassicalSixthRational
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
"""
            names = []
            for i in range(block * 16, (block + 1) * 16):
                p = points[i]
                thm = f'paid_{tag.lower()}_{i}'
                names.append(thm)
                text += f"""theorem {thm} : ({p['q']}:ℝ)/{K} ≤ value {lit(F(p['ratio']))} {lit(F(p['s']))} := by
  norm_num [value,WuSource.SrcFourEnclosure.logLo,Finset.sum_range_succ,QuarterTrim.alpha]

"""
            text += 'end WuPaper.ClassicalSixthRational\n' + ''.join((f'#print axioms WuPaper.ClassicalSixthRational.{t}\n' for t in names))
            out[name + '.lean'] = text
        data[tag.lower()] = {'n': N, 'sum': sum((p['q'] for p in points)), 'points': points}
    return (out, data)

def payment_sources(data):
    """Assemble exact integer sums and connect all 16-point blocks to the integrals."""
    root = {}
    K = 10 ** 12
    for tag, start, stop in [('Lower', '2', 'split'), ('Upper', 'split', 'endpoint')]:
        key = tag.lower()
        d = data[key]
        nums = [p['q'] for p in d['points']]
        s = """import WR2ClassicalSixthAssembly
noncomputable section
namespace WuPaper.ClassicalSixthRational
open Finset
"""
        for b in range(256):
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
        for b in range(256):
            s += f"""  | {b} => {key}Block{b:03d} (i%16)
"""
        s += f"""  | _ => 0
def {key}Payment (i : ℕ) : ℝ := ({key}Numerator i:ℝ)/{K}
"""
        s += f"""set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem {key}_sum : (∑ i ∈ range 4096, {key}Numerator i) = {d['sum']} := by
  decide +kernel

theorem {key}_total : ({d['sum']}:ℝ)/{K} ≤ ∑ i ∈ range 4096, {key}Payment i := by
  simp only [{key}Payment,← Finset.sum_div,← Nat.cast_sum,{key}_sum]
  rfl
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.{key}_total
"""
        root[f'WR2ClassicalSixth{tag}Payments.lean'] = s
        for b in range(256):
            s = f"""import WR2ClassicalSixth{tag}Payments
import WR2ClassicalSixth{tag}Points{b:03d}
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem {key}_grid_block_{b:03d} (j : Fin 16) : {key}Payment (16*{b}+j.val) ≤
    {key}Value ((point {start} {stop} 4096 (16*{b}+j.val)+point {start} {stop} 4096 (16*{b}+j.val+1))/2) := by
  fin_cases j
"""
            for j in range(16):
                i = 16 * b + j
                p = d['points'][i]
                x = F(p['s'])
                ratio = F(p['ratio'])
                lit = f'({x.numerator}:ℝ)/{x.denominator}'
                rr = f'({ratio.numerator}:ℝ)/{ratio.denominator}'
                exp = f'ClassicalSixthBranch.r*ClassicalSixthBranch.u ({lit})/ClassicalSixthBranch.v ({lit})' if key == 'lower' else f'ClassicalSixthBranch.u ({lit})*ClassicalSixthBranch.v ({lit})/ClassicalSixthBranch.r'
                s += f"""  · change {key}Payment {i} ≤ {key}Value ((point {start} {stop} 4096 {i}+point {start} {stop} 4096 {i + 1})/2)
    have hp : {key}Payment {i} = ({nums[i]}:ℝ)/{K} := rfl
    have hx : (point {start} {stop} 4096 {i}+point {start} {stop} 4096 {i + 1})/2 = {lit} := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : {exp} = {rr} := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold {key}Value
    rw [hr]
    exact paid_{key}_{i}
"""
            s += f"""end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.{key}_grid_block_{b:03d}
"""
            root[f'WR2ClassicalSixth{tag}GridBlock{b:03d}.lean'] = s
        s = ''.join((f'import WR2ClassicalSixth{tag}GridBlock{b:03d}\n' for b in range(256)))
        s += f"""noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxHeartbeats 4000000 in
theorem all_{key}_paid (i : ℕ) (hi : i < 4096) : {key}Payment i ≤
    {key}Value ((point {start} {stop} 4096 i+point {start} {stop} 4096 (i+1))/2) := by
  have hj : i%16 < 16 := Nat.mod_lt _ (by norm_num)
  have hb : i/16 < 256 := by omega
  have hh (b : Fin 256) : {key}Payment (16*b.val+i%16) ≤
      {key}Value ((point {start} {stop} 4096 (16*b.val+i%16)+point {start} {stop} 4096 (16*b.val+i%16+1))/2) := by
    fin_cases b
"""
        for b in range(256):
            s += f"""    · exact {key}_grid_block_{b:03d} ⟨i%16,hj⟩
"""
        s += f"""  have he : 16*(i/16)+i%16=i := by omega
  simpa only [he] using hh ⟨i/16,hb⟩
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.all_{key}_paid
"""
        root[f'WR2ClassicalSixth{tag}Root.lean'] = s
    s = """import WR2ClassicalSixthLowerRoot
import WR2ClassicalSixthUpperRoot
noncomputable section
namespace WuPaper.ClassicalSixthRational

theorem sixth_main_lower : (381909:ℝ)/100000 ≤ Wu08TerminalAlignment.sixthMain :=
  ClassicalSixthAssembly.sixth_lower_of_payments lowerPayment upperPayment
    all_lower_paid all_upper_paid lower_total upper_total

end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.sixth_main_lower
"""
    root['WR2ClassicalSixthCertificate.lean'] = s
    return root

def generate():
    sources, data = point_sources()
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
