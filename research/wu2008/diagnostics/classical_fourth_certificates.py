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

BQ_DATA = '''import WR2IntegerLogUpper
namespace WuPaper.ClassicalFourthData
open IntegerLogUpper

def BqRawNumerator (i : ℕ) : ℕ :=
  1000000000000000*4000*(hiNumerator i (16000+i)*hiDenominator i (16000+3*i)+
    hiNumerator i (16000+3*i)*hiDenominator i (16000+i))
def BqRawDenominator (i : ℕ) : ℕ :=
  (8000+i)*hiDenominator i (16000+i)*hiDenominator i (16000+3*i)
def Bq (i : ℕ) : ℕ :=
  if i ≤ 10540 then ClassicalCumulativeDivision.ceilDiv (BqRawNumerator i) (BqRawDenominator i) else 0
end WuPaper.ClassicalFourthData
'''

BQ_SOUNDNESS = '''import WR2ClassicalFourthDataBq
namespace WuPaper.FourthBqInteger
open IntegerLogUpper ClassicalFourthData

def splitUpper (t : ℚ) : ℚ :=
  (ExactRational.logHi ((1+(t-1))/2)+ExactRational.logHi (2*(t-1)/(1+(t-1))))/t

theorem combine (K S A B C D : ℚ) (hS : S ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) :
    K*4000*(A*D+B*C)/(S*C*D) = K*((A/C+B/D)/(S/4000)) := by
  field_simp [hS,hC,hD]

theorem rawDenominator_pos (i : ℕ) : 0 < BqRawDenominator i := by
  have hC := hiDenominator_pos (show i < 16000+i by omega)
  have hD := hiDenominator_pos (show i < 16000+3*i by omega)
  unfold BqRawDenominator
  exact Nat.mul_pos (Nat.mul_pos (by omega) hC) hD

theorem raw_fraction_eq (i : ℕ) :
    (BqRawNumerator i:ℚ)/(BqRawDenominator i:ℚ) =
      1000000000000000*splitUpper (2+(i:ℚ)/4000) := by
  have h1 := logHi_nat_ratio (show 8000 ≤ 8000+i by omega) (show 0 < (8000:ℕ) by omega)
  have h2 := logHi_nat_ratio (show 8000+i ≤ 8000+2*i by omega) (show 0 < 8000+i by omega)
  rw [show 8000+i-8000=i by omega,show 8000+i+8000=16000+i by omega] at h1
  rw [show 8000+2*i-(8000+i)=i by omega,show 8000+2*i+(8000+i)=16000+3*i by omega] at h2
  have hS : ((8000+i:ℕ):ℚ) ≠ 0 := by positivity
  have hC : (hiDenominator i (16000+i):ℚ) ≠ 0 := by
    exact_mod_cast (hiDenominator_pos (show i<16000+i by omega)).ne'
  have hD : (hiDenominator i (16000+3*i):ℚ) ≠ 0 := by
    exact_mod_cast (hiDenominator_pos (show i<16000+3*i by omega)).ne'
  have harg1 : ((8000+i:ℕ):ℚ)/((8000:ℕ):ℚ) = (1+((2+(i:ℚ)/4000)-1))/2 := by
    push_cast
    ring
  have harg2 : ((8000+2*i:ℕ):ℚ)/((8000+i:ℕ):ℚ) =
      2*((2+(i:ℚ)/4000)-1)/(1+((2+(i:ℚ)/4000)-1)) := by
    have hs : (8000:ℚ)+i ≠ 0 := by simpa only [Nat.cast_add,Nat.cast_ofNat] using hS
    have ht : 1+((2+(i:ℚ)/4000)-1) = (8000+(i:ℚ))/4000 := by ring
    rw [ht]
    push_cast
    field_simp [hs]
    ring
  rw [harg1] at h1
  rw [harg2] at h2
  have ht : (2+(i:ℚ)/4000) = ((8000+i:ℕ):ℚ)/4000 := by push_cast; ring
  unfold splitUpper
  rw [h1,h2,ht]
  simpa only [BqRawNumerator,BqRawDenominator,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using
    combine 1000000000000000 ((8000+i:ℕ):ℚ)
      (hiNumerator i (16000+i):ℚ) (hiNumerator i (16000+3*i):ℚ)
      (hiDenominator i (16000+i):ℚ) (hiDenominator i (16000+3*i):ℚ) hS hC hD

theorem Bq_paid {i : ℕ} (hi : i ≤ 10540) :
    splitUpper (2+(i:ℚ)/4000) ≤ (Bq i:ℚ)/1000000000000000 := by
  simpa only [Bq,if_pos hi,Nat.cast_ofNat] using
    ceil_payment_of_exact (rawDenominator_pos i)
      (show 0 < (1000000000000000:ℕ) by norm_num) (raw_fraction_eq i)

example : Bq 0 = 0 := by decide +kernel
example : Bq 10541 = 0 := by decide +kernel
end WuPaper.FourthBqInteger
#print axioms WuPaper.FourthBqInteger.Bq_paid
'''

BQ_ALL_LOG = '''import WR2ClassicalFourthTableCheck
import WR2ClassicalFourthBqSoundness
namespace WuPaper.ClassicalFourthConditions
theorem all_Log (i : ℕ) (hi : i < 10541) : WuPaper.ClassicalB.splitUpper (WuPaper.ClassicalFourthRecurrence.node 2 (i)) ≤ val WuPaper.ClassicalFourthData.Bq (i) := by
  apply ClassicalFourthTableCheck.logCondition_sound
  exact FourthBqInteger.Bq_paid (by omega)
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.all_Log
'''

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
        if key == 'Bq':
            root[name + '.lean'] = BQ_DATA
            continue
        if key == 'outerq':
            root[name + '.lean'] = """import WR2ClassicalFourthDataB
import WR2ClassicalFourthDataD
namespace WuPaper.ClassicalFourthData
/-- Exact ceiling of the outer integrand, with the original finite-table support. -/
def outerq (i : ℕ) : ℕ :=
  if i ≤ 10540 then
    let numerator := 2654*4000^2*(1000000000000000+B i+(if 8000 ≤ i then D (i-8000) else 0))
    let denominator := (12000+i)*(5308000-200*(12000+i))
    (numerator+denominator-1)/denominator
  else 0
end WuPaper.ClassicalFourthData
"""
            continue
        if key in ['B', 'outer', 'C', 'D']:
            error = {'B': 2, 'outer': 56, 'C': 2, 'D': 1}[key]
            if key in ['C', 'D']:
                parent, base = ('B', 12000) if key == 'C' else ('C', 16000)
                imports = f'import WR2ClassicalFourthData{parent}\nimport WR2ClassicalCumulativeDivision'
                definition = f'if i ≤ 2540 then ClassicalCumulativeTable.table (ClassicalCumulativeDivision.quotient {parent} {base}) {error} {key}Anchor i else 0'
            else:
                imports = f'import WR2ClassicalFourthData{key}q\nimport WR2ClassicalCumulativeTable'
                definition = f'ClassicalCumulativeTable.table {key}q {error} {key}Anchor i'
            s = f'''{imports}

namespace WuPaper.ClassicalFourthData

/-- Exact cumulative values at block boundaries; interior values follow the recurrence. -/
def {key}Anchor : ℕ → ℕ
'''
            anchors = nums[::4]
            # The second level keeps the integer matcher shallow as well.
            s = s.rsplit(f'def {key}Anchor : ℕ → ℕ\n', 1)[0]
            for block in range((len(anchors)+127)//128):
                s += f'def {key}AnchorBlock{block:03d} : ℕ → ℕ\n'
                for i, value in enumerate(anchors[128*block:128*(block+1)]):
                    s += f'  | {i} => {value}\n'
                s += '  | _ => 0\n'
            s += f'def {key}Anchor (i : ℕ) : ℕ :=\n  match i/128 with\n'
            for block in range((len(anchors)+127)//128):
                s += f'  | {block} => {key}AnchorBlock{block:03d} (i%128)\n'
            s += f'''  | _ => 0

def {key} (i : ℕ) : ℕ := {definition}

end WuPaper.ClassicalFourthData
'''
            root[name + '.lean'] = s
            continue
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
    return root

def ungrouped_coverage_sources(d):
    """Check unchanged tables directly; proof blocks do not change the mesh."""
    result = {}
    families = [('BPay', 'BPay', len(d['B'])-1, 256),
                ('CPay', 'CPay', len(d['C'])-1, 256),
                ('DPay', 'DPay', len(d['D'])-1, 256),
                ('outerPay', 'OuterPay', len(d['outer'])-1, 256),
                ('OuterPoint', 'OuterPoint', len(d['outerq']), 256),
                ('Log', '', len(d['Bq']), 64)]
    for key, condition, n, width in families:
        if key == 'Log':
            result['WR2ClassicalFourthAllLog.lean'] = BQ_ALL_LOG
            continue
        if key == 'OuterPoint':
            result['WR2ClassicalFourthAllOuterPoint.lean'] = """import WR2ClassicalFourthIntegerConditions
import WR2ClassicalCumulativeDivision
namespace WuPaper.ClassicalFourthConditions
/-- Every outer sample is paid by its defining ceiling; no pointwise checks are needed. -/
theorem all_OuterPoint (i : ℕ) (hi : i < 10541) : OuterPoint (i) := by
  have hi' : i ≤ 10540 := by omega
  have hd : 0 < (12000+i)*(5308000-200*(12000+i)) :=
    Nat.mul_pos (by omega) (by omega)
  unfold OuterPoint ClassicalFourthData.outerq tail
  rw [if_pos hi']
  exact ClassicalCumulativeDivision.ceilDiv_paid _ _ hd
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.all_OuterPoint
"""
            continue
        count = (n + width - 1) // width
        def prop(index):
            return f'{condition} ({index})'
        for block in range(count):
            index = f'{width}*{block}+j.val'
            imported = 'WR2ClassicalFourthIntegerConditions'
            proof_condition = condition
            proof = ''
            proof += f"""  exact (by unfold {proof_condition}; decide +kernel :
    ∀ j : Fin {width}, {width}*{block}+j.val < {n} → {proof_condition} ({index})) j hj
"""
            if key in ['BPay', 'outerPay']:
                table, error = ('B', 2) if key == 'BPay' else ('outer', 56)
                imported += '\nimport WR2ClassicalCumulativePayment'
                boundary = f'{width}*{block}+4*k.val+3'
                proof = f'''  by_cases hb : ({index})%4 ≠ 3
  · simpa only [{condition}, ClassicalFourthData.{table}] using
      ClassicalCumulativeTable.table_payment ClassicalFourthData.{table}q {error}
        ClassicalFourthData.{table}Anchor hj hb
  · have hk : j.val/4 < {width//4} := by omega
    have he : {index} = {width}*{block}+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold {condition}; decide +kernel :
      ∀ k : Fin {width//4}, {boundary} < {n} → {condition} ({boundary}))
      ⟨j.val/4,hk⟩ (by change {width}*{block}+4*(j.val/4)+3 < {n}; omega)
'''
            if key in ['CPay', 'DPay']:
                table, parent, base, error = ('C', 'B', 12000, 2) if key == 'CPay' else ('D', 'C', 16000, 1)
                imported += '\nimport WR2ClassicalCumulativeDivision'
                boundary = f'{width}*{block}+4*k.val+3'
                proof = f'''  by_cases hb : ({index})%4 ≠ 3
  · have h := ClassicalCumulativeDivision.divided_table_paid ClassicalFourthData.{parent} {base} {error}
      ClassicalFourthData.{table}Anchor (i := {index}) (by omega) hb (by omega)
    simpa only [{condition}, ClassicalFourthData.{table},
      if_pos (show {index} ≤ 2540 from Nat.le_of_lt hj), if_pos (show {index}+1 ≤ 2540 by omega)] using h
  · have hk : j.val/4 < {width//4} := by omega
    have he : {index} = {width}*{block}+4*(j.val/4)+3 := by omega
    rw [he]
    exact (by unfold {condition}; decide +kernel :
      ∀ k : Fin {width//4}, {boundary} < {n} → {condition} ({boundary}))
      ⟨j.val/4,hk⟩ (by change {width}*{block}+4*(j.val/4)+3 < {n}; omega)
'''
            result[f'WR2ClassicalFourthBlock{key}{block:03d}.lean'] = f"""import {imported}
namespace WuPaper.ClassicalFourthConditions
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem {key}_block_{block:03d} (j : Fin {width}) (hj : {index} < {n}) :
    {prop(index)} := by
{proof}
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.{key}_block_{block:03d}
"""
        text = ''.join(f'import WR2ClassicalFourthBlock{key}{b:03d}\n' for b in range(count))
        text += f"""noncomputable section
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
            text += f'    · exact {key}_block_{b:03d} ⟨i%{width},hj⟩\n'
        text += f"""  have he : {width}*(i/{width})+i%{width}=i := by omega
  have h := hh ⟨i/{width},hb⟩ (by change {width}*(i/{width})+i%{width} < {n}; omega)
  simpa only [he] using h
end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.all_{key}
"""
        result[f'WR2ClassicalFourthAll{key}.lean'] = text
    return result

LAYER_TEMPLATES = {
    'WR2ClassicalCumulativeTable.lean': r"""import Mathlib.Data.Nat.Basic

namespace WuPaper.ClassicalCumulativeTable

/-- Exact integer increment for a rounded trapezoid with its analytic error. -/
def increment (q : ℕ → ℕ) (E i : ℕ) : ℕ :=
  (3*4000^2*(q i+q (i+1))+E*1000000000000000+(6*4000^3-1))/(6*4000^3)

/-- Reconstruct only the short prefix following a stored block anchor. -/
def accumulate (q : ℕ → ℕ) (E anchor start : ℕ) : ℕ → ℕ
  | 0 => anchor
  | n+1 => accumulate q E anchor start n + increment q E (start+n)

/-- Anchors bound reduction depth without changing the cumulative table. -/
def table (q : ℕ → ℕ) (E : ℕ) (anchor : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i ≤ 10540 then accumulate q E (anchor (i/4)) (4*(i/4)) (i%4) else 0

end WuPaper.ClassicalCumulativeTable
""",
    'WR2ClassicalCumulativePayment.lean': r"""import WR2ClassicalCumulativeTable
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace WuPaper.ClassicalCumulativeTable

/-- The exact ceiling increment pays the rounded trapezoid and its error. -/
theorem increment_payment (q : ℕ → ℕ) (E i : ℕ) :
    3*4000^2*(q i+q (i+1))+E*1000000000000000 ≤
      6*4000^3*increment q E i := by
  unfold increment
  norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceSub]
  omega

/-- Every recursive step is paid without inspecting any concrete table entry. -/
theorem accumulate_payment (q : ℕ → ℕ) (E anchor start n : ℕ) :
    6*4000^3*accumulate q E anchor start n+
      3*4000^2*(q (start+n)+q (start+n+1))+E*1000000000000000 ≤
        6*4000^3*accumulate q E anchor start (n+1) := by
  rw [accumulate, Nat.mul_add]
  have h := increment_payment q E (start+n)
  omega

/-- Away from a block boundary, the reconstructed table takes one exact step. -/
theorem table_succ (q : ℕ → ℕ) (E : ℕ) (anchor : ℕ → ℕ) {i : ℕ}
    (hi : i < 10540) (hb : i%4 ≠ 3) :
    table q E anchor (i+1) = table q E anchor i+increment q E i := by
  have hi' : i+1 ≤ 10540 := by omega
  have hd : (i+1)/4 = i/4 := by omega
  have hm : (i+1)%4 = i%4+1 := by omega
  have he : 4*(i/4)+i%4 = i := by omega
  simp only [table, if_pos hi', if_pos hi.le, hd, hm, accumulate, he]

/-- Interior payments follow from the recurrence, not from finite table reduction. -/
theorem table_payment (q : ℕ → ℕ) (E : ℕ) (anchor : ℕ → ℕ) {i : ℕ}
    (hi : i < 10540) (hb : i%4 ≠ 3) :
    6*4000^3*table q E anchor i+
      3*4000^2*(q i+q (i+1))+E*1000000000000000 ≤
        6*4000^3*table q E anchor (i+1) := by
  rw [table_succ q E anchor hi hb, Nat.mul_add]
  have h := increment_payment q E i
  omega

end WuPaper.ClassicalCumulativeTable

#print axioms WuPaper.ClassicalCumulativeTable.increment_payment
#print axioms WuPaper.ClassicalCumulativeTable.accumulate_payment
#print axioms WuPaper.ClassicalCumulativeTable.table_succ
#print axioms WuPaper.ClassicalCumulativeTable.table_payment
""",
    'WR2ClassicalCumulativeDivision.lean': r"""import WR2ClassicalCumulativePayment
import Mathlib.Tactic.Linarith

namespace WuPaper.ClassicalCumulativeDivision
open ClassicalCumulativeTable

def ceilDiv (n d : ℕ) : ℕ := (n+d-1)/d

def quotient (q : ℕ → ℕ) (base i : ℕ) : ℕ := ceilDiv (4000*q i) (base+i)

theorem ceilDiv_paid (n d : ℕ) (hd : 0 < d) : n ≤ d*ceilDiv n d := by
  have hm := Nat.mod_lt (n+d-1) hd
  have he := Nat.div_add_mod (n+d-1) d
  unfold ceilDiv
  omega

theorem quotient_paid (q : ℕ → ℕ) (base i : ℕ) (hm : 0 < base+i) :
    4000*q i ≤ (base+i)*quotient q base i := ceilDiv_paid _ _ hm

/-- Multiplying the rounded endpoint bounds shows that they pay the exact divided values. -/
theorem divided_step_paid (q : ℕ → ℕ) (base E i p : ℕ) (hm : 0 < base+i) :
    let m := base+i
    6*4000^3*m*(m+1)*p+
      3*4000^3*((m+1)*q i+m*q (i+1))+E*1000000000000000*m*(m+1) ≤
        6*4000^3*m*(m+1)*(p+increment (quotient q base) E i) := by
  dsimp only
  have h0 := quotient_paid q base i hm
  have h1 := quotient_paid q base (i+1) (by omega)
  have h0' := Nat.mul_le_mul_left (base+i+1) h0
  have h1' := Nat.mul_le_mul_left (base+i) h1
  have hs := increment_payment (quotient q base) E i
  have hs' := Nat.mul_le_mul_left ((base+i)*(base+i+1)) hs
  nlinarith only [h0',h1',hs']

theorem divided_table_paid (q : ℕ → ℕ) (base E : ℕ) (anchor : ℕ → ℕ) {i : ℕ}
    (hi : i < 10540) (hb : i%4 ≠ 3) (hm : 0 < base+i) :
    let m := base+i
    6*4000^3*m*(m+1)*table (quotient q base) E anchor i+
      3*4000^3*((m+1)*q i+m*q (i+1))+E*1000000000000000*m*(m+1) ≤
        6*4000^3*m*(m+1)*table (quotient q base) E anchor (i+1) := by
  dsimp only
  rw [table_succ (quotient q base) E anchor hi hb]
  exact divided_step_paid q base E i _ hm

end WuPaper.ClassicalCumulativeDivision
#print axioms WuPaper.ClassicalCumulativeDivision.divided_step_paid
""",
    'WR2ClassicalFourthIntegerConditions.lean': r"""import WR2ClassicalFourthDataBq
import WR2ClassicalFourthDataB
import WR2ClassicalFourthDataC
import WR2ClassicalFourthDataD
import WR2ClassicalFourthDataouterq
import WR2ClassicalFourthDataouter

namespace WuPaper.ClassicalFourthConditions
open ClassicalFourthData

def BPay (i : ℕ) : Prop :=
  6*4000^3*B i+3*4000^2*(Bq i+Bq (i+1))+2*1000000000000000 ≤ 6*4000^3*B (i+1)
def CPay (i : ℕ) : Prop :=
  let m := 12000+i
  6*4000^3*m*(m+1)*C i+3*4000^3*((m+1)*B i+m*B (i+1))+2*1000000000000000*m*(m+1) ≤
    6*4000^3*m*(m+1)*C (i+1)
def DPay (i : ℕ) : Prop :=
  let m := 16000+i
  6*4000^3*m*(m+1)*D i+3*4000^3*((m+1)*C i+m*C (i+1))+1*1000000000000000*m*(m+1) ≤
    6*4000^3*m*(m+1)*D (i+1)
def OuterPay (i : ℕ) : Prop :=
  6*4000^3*outer i+3*4000^2*(outerq i+outerq (i+1))+56*1000000000000000 ≤ 6*4000^3*outer (i+1)
def tail (i : ℕ) : ℕ := if 8000 ≤ i then D (i-8000) else 0
def OuterPoint (i : ℕ) : Prop :=
  2654*4000^2*(1000000000000000+B i+tail i) ≤ (12000+i)*(5308000-200*(12000+i))*outerq i

end WuPaper.ClassicalFourthConditions
""",
    'WR2ClassicalFourthConditions.lean': r"""import WR2ClassicalFourthIntegerConditions
import WR2ClassicalFourthAssembly
import WR2ClassicalIntegerPayments

noncomputable section
namespace WuPaper.ClassicalFourthConditions
open Real ClassicalFourthData ClassicalFourthRecurrence

abbrev val (f : ℕ → ℕ) (i : ℕ) : ℝ := (f i:ℝ)/1000000000000000

theorem B_payment {i : ℕ} (h : BPay i) :
    (1:ℝ)/4000*(val Bq i+val Bq (i+1))/2+2*((1:ℝ)/4000)^3/6 ≤ val B (i+1)-val B i :=
  ClassicalIntegerPayments.direct_payment _ _ _ _ 2 h

theorem C_payment {i : ℕ} (h : CPay i) :
    (1:ℝ)/4000*(val B i/node 3 i+val B (i+1)/node 3 (i+1))/2+
      2*((1:ℝ)/4000)^3/6 ≤ val C (i+1)-val C i := by
  have hm : node 3 i = ((12000+i:ℕ):ℝ)/4000 := by simp [node]; ring
  have hn : node 3 (i+1) = (((12000+i:ℕ):ℝ)+1)/4000 := by simp [node]; ring
  rw [hm,hn]
  exact ClassicalIntegerPayments.divided_payment (12000+i) _ _ _ _ 2 (by omega) h

theorem D_payment {i : ℕ} (h : DPay i) :
    (1:ℝ)/4000*(val C i/node 4 i+val C (i+1)/node 4 (i+1))/2+
      1*((1:ℝ)/4000)^3/6 ≤ val D (i+1)-val D i := by
  have hm : node 4 i = ((16000+i:ℕ):ℝ)/4000 := by simp [node]; ring
  have hn : node 4 (i+1) = (((16000+i:ℕ):ℝ)+1)/4000 := by simp [node]; ring
  rw [hm,hn]
  simpa only [Nat.cast_one] using ClassicalIntegerPayments.divided_payment (16000+i) _ _ _ _ 1 (by omega) h

theorem outer_payment {i : ℕ} (h : OuterPay i) :
    (1:ℝ)/4000*(val outerq i+val outerq (i+1))/2+56*((1:ℝ)/4000)^3/6 ≤
      val outer (i+1)-val outer i := ClassicalIntegerPayments.direct_payment _ _ _ _ 56 h

theorem outer_point {i : ℕ} (hi : i ≤ 10540) (h : OuterPoint i) :
    (1+val B i+val tail i)/(node 3 i*((1:ℝ)/2-(100/1327)*node 3 i)) ≤ val outerq i := by
  have hm : node 3 i = ((12000+i:ℕ):ℝ)/4000 := by simp [node]; ring
  have hw : 0 < 5308000-200*(12000+i) := by omega
  have hsub : 200*(12000+i) ≤ 5308000 := by omega
  have ht : (1:ℝ)/2-(100/1327)*node 3 i =
      ((5308000-200*(12000+i):ℕ):ℝ)/(2654*4000) := by
    rw [Nat.cast_sub hsub]
    push_cast
    unfold node
    ring
  rw [ht,hm]
  exact ClassicalIntegerPayments.outer_payment (12000+i) (5308000-200*(12000+i)) _ _ _ (by omega) hw h

end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.C_payment
#print axioms WuPaper.ClassicalFourthConditions.outer_point
""",
}

def coverage_sources(d):
    """Retain independent proofs and scoped budgets in eight-block containers."""
    sources = ungrouped_coverage_sources(d)
    for family in ('BPay', 'CPay', 'DPay', 'outerPay'):
        prefix = f'WR2ClassicalFourthBlock{family}'
        blocks = sorted(name for name in sources if name.startswith(prefix))
        containers = []
        for first in range(0, len(blocks), 8):
            subset = blocks[first:first+8]
            name = f'WR2ClassicalFourth{family}Batch{first//8:03d}.lean'
            containers.append(name[:-5])
            imports = list(dict.fromkeys(line+'\n' for n in subset
                for line in sources[n].splitlines() if line.startswith('import ')))
            body = ''.join(imports)+'namespace WuPaper.ClassicalFourthConditions\n\n'
            for block in subset:
                old = sources.pop(block)
                body += old[old.index('set_option maxRecDepth'):old.index('end WuPaper.ClassicalFourthConditions')]
            sources[name] = body+'end WuPaper.ClassicalFourthConditions\n'
        name = f'WR2ClassicalFourthAll{family}.lean'
        old = sources[name]
        body = old[old.index('noncomputable section'):]
        sources[name] = 'import Mathlib.Tactic.FinCases\n'+''.join('import '+n+'\n' for n in containers)+body
    sources.update(LAYER_TEMPLATES)
    return sources

def generate():
    data = table_data()
    sources = {'WR2ClassicalFourthBqSoundness.lean': BQ_SOUNDNESS}
    for render in (natural_sources, coverage_sources):
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
