#!/usr/bin/env python3
"""Reproduce fourth-slot tables and finite certificates using exact rational arithmetic.

The mesh is 1/4000 and every upper payment is rounded up at scale 10^15.
Twelve-term logarithm bounds and trapezoid error payments determine the
B, C, D and outer tables. No stored tables or third-party packages are used.
Generated-source comparison does not replace Lean proof verification.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse

def table_data():
    nunit = 4000
    h = F(1, nunit)
    N = 527 * nunit // 200
    scale = 10 ** 15
    alpha = F(100, 1327)

    def ceilq(x):
        return F(-(-x.numerator * scale // x.denominator), scale)

    def loghi(x):
        z = (x - 1) / (x + 1)
        return 2 * sum((z ** (2 * j + 1) / F(2 * j + 1) for j in range(12))) + 2 * z ** 25 / (1 - z * z)

    def split(x):
        return loghi((1 + x) / 2) + loghi(2 * x / (1 + x))
    q = [ceilq(split(1 + i * h) / (2 + i * h)) for i in range(N + 1)]

    def cumulative(q, B):
        p = [F(0)]
        for i in range(len(q) - 1):
            p.append(ceilq(p[-1] + h * (q[i] + q[i + 1]) / 2 + B * h ** 3 / 6))
        return p
    bs = cumulative(q, 2)
    cs = cumulative([ceilq(v / (3 + i * h)) for i, v in enumerate(bs[:N - 2 * nunit + 1])], 2)
    ds = cumulative([ceilq(v / (4 + i * h)) for i, v in enumerate(cs)], 1)
    f = []
    for i in range(N + 1):
        s = 3 + i * h
        A = 1 + bs[i] + (ds[i - 2 * nunit] if i >= 2 * nunit else 0)
        f.append(ceilq(A / (s * (F(1, 2) - alpha * s))))
    outer = cumulative(f, 56)
    return {'unit': nunit, 'scale': scale, 'Bq': [int(x * scale) for x in q], 'B': [int(x * scale) for x in bs], 'C': [int(x * scale) for x in cs], 'D': [int(x * scale) for x in ds], 'outerq': [int(x * scale) for x in f], 'outer': [int(x * scale) for x in outer]}

def natural_sources(d):
    root = {}
    H = d['unit']
    K = d['scale']
    for key in ['Bq', 'B', 'C', 'D', 'outerq', 'outer']:
        nums = d[key]
        name = 'WR2ClassicalFourthData' + key
        s = """import WR2ClassicalIntegerPayments
namespace WuPaper.ClassicalFourthData
"""
        for block in range((len(nums) + 127) // 128):
            s += f"""def {key}Block{block:03d} : ℕ → ℕ
"""
            for j, v in enumerate(nums[128 * block:128 * (block + 1)]):
                s += f"""  | {j} => {v}
"""
            s += """  | _ => 0
"""
        s += f"""def {key} (i : ℕ) : ℕ :=
  match i/128 with
"""
        for block in range((len(nums) + 127) // 128):
            s += f"""  | {block} => {key}Block{block:03d} (i%128)
"""
        s += """  | _ => 0
end WuPaper.ClassicalFourthData
"""
        root[name + '.lean'] = s
    conditions = {}
    for key, qkey, E in [('B', 'Bq', 2), ('outer', 'outerq', 56)]:
        nums = d[key]
        q = d[qkey]
        rows = []
        for i in range(len(nums) - 1):
            lhs = 6 * H ** 3 * nums[i] + 3 * H ** 2 * (q[i] + q[i + 1]) + E * K
            rhs = 6 * H ** 3 * nums[i + 1]
            assert lhs <= rhs
            rows.append(f'6*4000^3*{nums[i]}+3*4000^2*({q[i]}+{q[i + 1]})+{E}*{K} ≤ 6*4000^3*{nums[i + 1]}')
        conditions[key + 'Pay'] = rows
    for key, qkey, offset, E in [('C', 'B', 3, 2), ('D', 'C', 4, 1)]:
        nums = d[key]
        q = d[qkey]
        rows = []
        for i in range(len(nums) - 1):
            m = offset * H + i
            lhs = 6 * H ** 3 * m * (m + 1) * nums[i] + 3 * H ** 3 * ((m + 1) * q[i] + m * q[i + 1]) + E * K * m * (m + 1)
            rhs = 6 * H ** 3 * m * (m + 1) * nums[i + 1]
            assert lhs <= rhs
            rows.append(f'6*4000^3*{m}*({m}+1)*{nums[i]}+3*4000^3*(({m}+1)*{q[i]}+{m}*{q[i + 1]})+{E}*{K}*{m}*({m}+1) ≤ 6*4000^3*{m}*({m}+1)*{nums[i + 1]}')
        conditions[key + 'Pay'] = rows
    rows = []
    for i, q in enumerate(d['outerq']):
        m = 3 * H + i
        w = 1327 * H - 200 * m
        a = d['B'][i]
        b = d['D'][i - 2 * H] if i >= 2 * H else 0
        assert 2654 * H ** 2 * (K + a + b) <= m * w * q
        rows.append(f'2654*4000^2*({K}+{a}+{b}) ≤ {m}*{w}*{q}')
    conditions['OuterPoint'] = rows
    for key, rows in conditions.items():
        for block in range((len(rows) + 63) // 64):
            s = """import WR2ClassicalIntegerPayments
namespace WuPaper.ClassicalFourthNat
"""
            for i in range(64 * block, min(64 * (block + 1), len(rows))):
                s += f"""theorem {key}_{i} : ({rows[i]} : Prop) := by decide +kernel
"""
            s += """end WuPaper.ClassicalFourthNat
"""
            s += f"""#print axioms WuPaper.ClassicalFourthNat.{key}_{64 * block}
"""
            root[f'WR2ClassicalFourthNat{key}{block:03d}.lean'] = s
    return root

def log_sources(d):
    root = {}
    nums = d['Bq']
    unit = d['unit']
    scale = d['scale']
    for block in range((len(nums) + 15) // 16):
        start = 16 * block
        end = min(start + 16, len(nums))
        s = """import WR2ClassicalBTrapezoid
noncomputable section
namespace WuPaper.ClassicalFourthLogPoints
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
"""
        for i in range(start, end):
            t = F(2) + F(i, unit)
            s += f"""theorem log_paid_{i} : WuPaper.ClassicalB.splitUpper (({t.numerator}:ℝ)/{t.denominator}) ≤ ({nums[i]}:ℝ)/{scale} := by
  norm_num [WuPaper.ClassicalB.splitUpper,WuPaper.ClassicalLogSplit.upper,
    WuSource.SrcFourEnclosure.logHi,WuSource.SrcFourEnclosure.logLo,Finset.sum_range_succ]

"""
        s += """end WuPaper.ClassicalFourthLogPoints
"""
        for i in range(start, end):
            s += f"""#print axioms WuPaper.ClassicalFourthLogPoints.log_paid_{i}
"""
        root[f'WR2ClassicalFourthLogPoints{block:03d}.lean'] = s
    root['WR2ClassicalFourthLogPointsRoot.lean'] = ''.join((f'import WR2ClassicalFourthLogPoints{b:03d}\n' for b in range((len(nums) + 15) // 16)))
    return root

def coverage_sources(d):
    r = {}
    families = [('BPay', 'BPay', 10540, 64), ('CPay', 'CPay', 2540, 64), ('DPay', 'DPay', 2540, 64), ('outerPay', 'OuterPay', 10540, 64), ('OuterPoint', 'OuterPoint', 10541, 64), ('Log', '', 10541, 16)]
    for key, cond, n, width in families:
        count = (n + width - 1) // width

        def prop(i):
            if key == 'Log':
                return f'WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 ({i})) ≤ val WuPaper.ClassicalFourthData.Bq ({i})'
            return f'{cond} ({i})'
        for block in range(count):
            imp = f'WR2ClassicalFourthLogPoints{block:03d}' if key == 'Log' else f'WR2ClassicalFourthNat{key}{block:03d}'
            s = f"""import WR2ClassicalFourthConditions
import {imp}
noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem {key}_block_{block:03d} (j : Fin {width}) (hj : {width}*{block}+j.val < {n}) :
    {prop(f'{width}*{block}+j.val')} := by
  fin_cases j
"""
            for j in range(width):
                i = block * width + j
                if i >= n:
                    s += """  · norm_num at hj
"""
                    continue
                if key != 'Log':
                    s += f"""  · exact WuPaper.ClassicalFourthNat.{key}_{i}
"""
                else:
                    t = F(2) + F(i, 4000)
                    num = d['Bq'][i]
                    s += f"""  · change WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 {i}) ≤ val WuPaper.ClassicalFourthData.Bq {i}
    have hp : val WuPaper.ClassicalFourthData.Bq {i} = ({num}:ℝ)/1000000000000000 := by
      have hn : WuPaper.ClassicalFourthData.Bq {i} = {num} := rfl
      norm_num [val,hn]
    have hx : WuPaper.ClassicalFourthRecurrence.node 2 {i} = ({t.numerator}:ℝ)/{t.denominator} := by norm_num [WuPaper.ClassicalFourthRecurrence.node]
    rw [hp,hx]
    exact WuPaper.ClassicalFourthLogPoints.log_paid_{i}
"""
            s += f"""end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.{key}_block_{block:03d}
"""
            r[f'WR2ClassicalFourthBlock{key}{block:03d}.lean'] = s
        s = ''.join((f'import WR2ClassicalFourthBlock{key}{b:03d}\n' for b in range(count)))
        s += f"""noncomputable section
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
theorem all_{key} (i : ℕ) (hi : i < {n}) : {prop('i')} := by
  have hj : i%{width} < {width} := Nat.mod_lt _ (by norm_num)
  have hb : i/{width} < {count} := by omega
  have hh (b : Fin {count}) : {width}*b.val+i%{width} < {n} → {prop(f'{width}*b.val+i%{width}')} := by
    fin_cases b
"""
        for b in range(count):
            s += f"""    · exact {key}_block_{b:03d} ⟨i%{width},hj⟩
"""
        s += f"""  have he : {width}*(i/{width})+i%{width}=i := by omega
  have h := hh ⟨i/{width},hb⟩ (by change {width}*(i/{width})+i%{width} < {n}; omega)
  simpa only [he] using h
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.all_{key}
"""
        r[f'WR2ClassicalFourthAll{key}.lean'] = s
    return r

def generate():
    data = table_data()
    sources = {}
    for render in (natural_sources, log_sources, coverage_sources):
        batch = render(data)
        assert not sources.keys() & batch.keys()
        sources.update(batch)
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
