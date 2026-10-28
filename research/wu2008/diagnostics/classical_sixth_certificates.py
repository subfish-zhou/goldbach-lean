#!/usr/bin/env python3
"""Reproduce the sixth classical-slot midpoint certificates using exact rationals.

The unchanged 8192 payments are computed by integer homogeneous log polynomials.
Generic soundness replaces pointwise rational checks. Independent 64-point
integer sums retain both original totals. Exact Fraction computations below
verify every generated payment; Lean separately checks proofs and sums.
"""
from fractions import Fraction as F
from pathlib import Path
import argparse

def point_data():
    """Round each of the two 4096-point midpoint grids down to scale 10^12."""
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
        data[tag.lower()] = {'n': N, 'sum': sum((p['q'] for p in points)), 'points': points}
    return data

FIXED_SOURCES = {
    'WR2ClassicalSixthIntegerData.lean': r"""import Mathlib.Data.Real.Basic
import WR2IntegerLogHorner
namespace WuPaper.SixthIntegerPayment
open IntegerLogHorner

def scale : ℕ := 1000000000000
def gridDenominator : ℕ := 168755200
def gridNumerator (upper : Bool) (i : ℕ) : ℕ :=
  if upper then 576151552+12575*(2*i+1) else 337510400+29131*(2*i+1)
def uNumerator (upper : Bool) (i : ℕ) : ℕ :=
  1127*gridDenominator-200*gridNumerator upper i
def vNumerator (upper : Bool) (i : ℕ) : ℕ :=
  828048*gridDenominator-164800*gridNumerator upper i
def weightNumerator (upper : Bool) (i : ℕ) : ℕ :=
  1327*gridDenominator-200*gridNumerator upper i
def ratioNumerator (upper : Bool) (i : ℕ) : ℕ :=
  if upper then uNumerator upper i*vNumerator upper i else 1327*uNumerator upper i
def ratioDenominator (upper : Bool) (i : ℕ) : ℕ :=
  if upper then 53080000*gridDenominator^2 else vNumerator upper i
def rawNumerator (upper : Bool) (i : ℕ) : ℕ :=
  scale*1327*gridDenominator^2*
    numerator (ratioNumerator upper i-ratioDenominator upper i)
      (ratioNumerator upper i+ratioDenominator upper i)*
    numerator (gridNumerator upper i-2*gridDenominator) (gridNumerator upper i)
def rawDenominator (upper : Bool) (i : ℕ) : ℕ :=
  denominator (ratioNumerator upper i+ratioDenominator upper i)*
    denominator (gridNumerator upper i)*gridNumerator upper i*weightNumerator upper i
def paymentNumerator (upper : Bool) (i : ℕ) : ℕ :=
  if i < 4096 then rawNumerator upper i/rawDenominator upper i else 0
end WuPaper.SixthIntegerPayment

namespace WuPaper.ClassicalSixthRational
abbrev lowerNumerator := SixthIntegerPayment.paymentNumerator false
noncomputable def lowerPayment (i : ℕ) : ℝ := (lowerNumerator i:ℝ)/1000000000000
def lowerPaymentBlockSum (b : ℕ) : ℕ := ∑ j ∈ Finset.range 64, lowerNumerator (64*b+j)
end WuPaper.ClassicalSixthRational

namespace WuPaper.ClassicalSixthRational
abbrev upperNumerator := SixthIntegerPayment.paymentNumerator true
noncomputable def upperPayment (i : ℕ) : ℝ := (upperNumerator i:ℝ)/1000000000000
def upperPaymentBlockSum (b : ℕ) : ℕ := ∑ j ∈ Finset.range 64, upperNumerator (64*b+j)
end WuPaper.ClassicalSixthRational
""",
    'WR2ClassicalSixthIntegerSoundness.lean': r"""import WR2ClassicalSixthIntegerData
import WR2ClassicalSixthTableCheck
set_option maxRecDepth 3000
set_option maxHeartbeats 40000
namespace WuPaper.SixthIntegerPayment
open IntegerLogHorner

theorem upper_abstract (U V : ℕ) (hu : 54356435000 ≤ U) (hv : 27812929320000 ≤ V) :
    53080000*gridDenominator^2 ≤ U*V ∧ 0 < 53080000*gridDenominator^2 := by
  constructor
  · have h : 53080000*gridDenominator^2 ≤ 54356435000*27812929320000 := by
      norm_num [gridDenominator]
    exact h.trans (Nat.mul_le_mul hu hv)
  · norm_num [gridDenominator]

theorem lower_abstract (U V : ℕ) (hu : 70187110400 ≤ U)
    (hv : V ≤ 84115691929600) (hp : 27812929320000 ≤ V) :
    V ≤ 1327*U ∧ 0 < V := by
  have h : 84115691929600 ≤ 1327*70187110400 := by norm_num
  exact ⟨hv.trans (h.trans (Nat.mul_le_mul_left 1327 hu)), by omega⟩

theorem grid_bounds (upper : Bool) {i : ℕ} (hi : i < 4096) :
    2*gridDenominator ≤ gridNumerator upper i ∧ gridNumerator upper i ≤ 679153377 := by
  cases upper <;> dsimp [gridNumerator,gridDenominator] <;> omega

theorem linear_bounds (upper : Bool) {i : ℕ} (hi : i < 4096) :
    54356435000 ≤ uNumerator upper i ∧ 27812929320000 ≤ vNumerator upper i ∧
      88107475000 ≤ weightNumerator upper i := by
  have h := grid_bounds upper hi
  dsimp [uNumerator,vNumerator,weightNumerator,gridDenominator] at *
  omega

theorem lower_s_max {i : ℕ} (hi : i < 4096) : gridNumerator false i ≤ 600000000 := by
  dsimp [gridNumerator]
  omega

theorem lower_u_min {i : ℕ} (hi : i < 4096) : 70187110400 ≤ uNumerator false i := by
  have hs := lower_s_max hi
  dsimp [uNumerator,gridDenominator]
  omega

theorem lower_v_max {i : ℕ} (hi : i < 4096) : vNumerator false i ≤ 84115691929600 := by
  have hs := (grid_bounds false hi).1
  dsimp [vNumerator,gridDenominator] at *
  omega

theorem ratio_bounds_upper {i : ℕ} (hi : i < 4096) :
    ratioDenominator true i ≤ ratioNumerator true i ∧ 0 < ratioDenominator true i := by
  simp only [ratioDenominator,ratioNumerator,↓reduceIte]
  exact upper_abstract (uNumerator true i) (vNumerator true i)
    (linear_bounds true hi).1 (linear_bounds true hi).2.1

theorem ratio_bounds_lower {i : ℕ} (hi : i < 4096) :
    ratioDenominator false i ≤ ratioNumerator false i ∧ 0 < ratioDenominator false i := by
  simp only [ratioDenominator,ratioNumerator,Bool.false_eq_true,↓reduceIte]
  exact lower_abstract (uNumerator false i) (vNumerator false i)
    (lower_u_min hi) (lower_v_max hi) (linear_bounds false hi).2.1

theorem ratio_bounds (upper : Bool) {i : ℕ} (hi : i < 4096) :
    ratioDenominator upper i ≤ ratioNumerator upper i ∧ 0 < ratioDenominator upper i := by
  cases upper
  · exact ratio_bounds_lower hi
  · exact ratio_bounds_upper hi


def rationalRatio (upper : Bool) (s : ℚ) : ℚ :=
  if upper then ClassicalSixthTableCheck.u s*ClassicalSixthTableCheck.v s/ClassicalSixthTableCheck.r
  else ClassicalSixthTableCheck.r*ClassicalSixthTableCheck.u s/ClassicalSixthTableCheck.v s
def rationalValue (upper : Bool) (s : ℚ) : ℚ := ClassicalSixthTableCheck.value (rationalRatio upper s) s

theorem midpoint_lower (i : ℕ) :
    (gridNumerator false i:ℚ)/(gridDenominator:ℚ) =
      ExactRational.midpoint 2 ClassicalSixthTableCheck.split 4096 i := by
  simp only [gridNumerator,gridDenominator,ExactRational.midpoint,
    ClassicalSixthTableCheck.split,Nat.cast_ofNat]
  norm_num
  ring

theorem midpoint_upper (i : ℕ) :
    (gridNumerator true i:ℚ)/(gridDenominator:ℚ) =
      ExactRational.midpoint ClassicalSixthTableCheck.split ClassicalSixthTableCheck.endpoint 4096 i := by
  simp only [gridNumerator,gridDenominator,ExactRational.midpoint,
    ClassicalSixthTableCheck.split,ClassicalSixthTableCheck.endpoint,
    Nat.cast_ofNat]
  norm_num
  ring

theorem u_grid (upper : Bool) {i : ℕ} (hi : i < 4096) :
    ClassicalSixthTableCheck.u ((gridNumerator upper i:ℚ)/gridDenominator) =
      (uNumerator upper i:ℚ)/(200*gridDenominator) := by
  have hg := grid_bounds upper hi
  have hu : 200*gridNumerator upper i ≤ 1127*gridDenominator := by
    dsimp [gridDenominator] at *; omega
  rw [uNumerator,Nat.cast_sub hu]
  push_cast
  norm_num [ClassicalSixthTableCheck.u,ClassicalSixthTableCheck.R,gridDenominator]
  ring

theorem v_grid (upper : Bool) {i : ℕ} (hi : i < 4096) :
    ClassicalSixthTableCheck.v ((gridNumerator upper i:ℚ)/gridDenominator) =
      (vNumerator upper i:ℚ)/(164800*gridDenominator) := by
  have hg := grid_bounds upper hi
  have hv : 164800*gridNumerator upper i ≤ 828048*gridDenominator := by
    dsimp [gridDenominator] at *; omega
  rw [vNumerator,Nat.cast_sub hv]
  push_cast
  norm_num [ClassicalSixthTableCheck.v,ClassicalSixthTableCheck.R,ClassicalSixthTableCheck.r,gridDenominator]
  ring

/-- Rational branch algebra is kept separate from the degree-23 log identities. -/
theorem lower_ratio_algebra (U V D : ℚ) (hD : D ≠ 0) (hV : V ≠ 0) :
    (1327/824)*(U/(200*D))/(V/(164800*D)) = 1327*U/V := by
  field_simp [hD,hV]
  ring

theorem upper_ratio_algebra (U V D : ℚ) (hD : D ≠ 0) :
    (U/(200*D))*(V/(164800*D))/(1327/824) = U*V/(53080000*D^2) := by
  field_simp [hD]
  ring

theorem ratio_grid (upper : Bool) {i : ℕ} (hi : i < 4096) :
    rationalRatio upper ((gridNumerator upper i:ℚ)/gridDenominator) =
      (ratioNumerator upper i:ℚ)/(ratioDenominator upper i:ℚ) := by
  have hd : (gridDenominator:ℚ) ≠ 0 := by norm_num [gridDenominator]
  have hv : (vNumerator upper i:ℚ) ≠ 0 := by
    exact_mod_cast (show vNumerator upper i ≠ 0 by have h := linear_bounds upper hi; omega)
  unfold rationalRatio
  cases upper
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [u_grid false hi,v_grid false hi]
    simpa only [ClassicalSixthTableCheck.r,ratioNumerator,ratioDenominator,
      Bool.false_eq_true,↓reduceIte,Nat.cast_mul,Nat.cast_ofNat] using
      lower_ratio_algebra (uNumerator false i:ℚ) (vNumerator false i:ℚ) (gridDenominator:ℚ) hd hv
  · simp only [↓reduceIte]
    rw [u_grid true hi,v_grid true hi]
    simpa only [ClassicalSixthTableCheck.r,ratioNumerator,ratioDenominator,
      ↓reduceIte,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      upper_ratio_algebra (uNumerator true i:ℚ) (vNumerator true i:ℚ) (gridDenominator:ℚ) hd

theorem weight_grid (upper : Bool) {i : ℕ} (hi : i < 4096) :
    1-2*(100/1327)*((gridNumerator upper i:ℚ)/gridDenominator) =
      (weightNumerator upper i:ℚ)/(1327*gridDenominator) := by
  have hg := grid_bounds upper hi
  have hw : 200*gridNumerator upper i ≤ 1327*gridDenominator := by
    dsimp [gridDenominator] at *; omega
  rw [weightNumerator,Nat.cast_sub hw]
  push_cast
  norm_num [gridDenominator]
  ring

theorem scaled_product (K D S W A B C E : ℚ) (hD : D ≠ 0) :
    K*1327*D^2*A*B/(C*E*S*W) =
      K*((A/C)*(B/E)/((S/D)*(W/(1327*D)))) := by
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  field_simp [hD]

theorem raw_fraction_eq (upper : Bool) {i : ℕ} (hi : i < 4096) :
    (rawNumerator upper i:ℚ)/(rawDenominator upper i:ℚ) =
      (scale:ℚ)*rationalValue upper ((gridNumerator upper i:ℚ)/gridDenominator) := by
  have hg := grid_bounds upper hi
  have hr := ratio_bounds upper hi
  have hd : 0 < gridDenominator := by decide
  have hs : gridDenominator ≤ gridNumerator upper i := by omega
  have hs' : gridDenominator ≤ gridNumerator upper i-gridDenominator := by omega
  have hfirst := logLo_nat_ratio hr.1 hr.2
  have hsecond := logLo_nat_ratio hs' hd
  rw [show gridNumerator upper i-gridDenominator-gridDenominator =
      gridNumerator upper i-2*gridDenominator by omega,
    show gridNumerator upper i-gridDenominator+gridDenominator = gridNumerator upper i by omega] at hsecond
  have harg : ((gridNumerator upper i-gridDenominator:ℕ):ℚ)/(gridDenominator:ℚ) =
      (gridNumerator upper i:ℚ)/(gridDenominator:ℚ)-1 := by
    rw [Nat.cast_sub hs]
    norm_num [gridDenominator]
    ring
  rw [harg] at hsecond
  unfold rationalValue ClassicalSixthTableCheck.value
  rw [ratio_grid upper hi,hfirst,hsecond,weight_grid upper hi]
  simpa only [rawNumerator,rawDenominator,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
    scaled_product (scale:ℚ) (gridDenominator:ℚ) (gridNumerator upper i:ℚ)
      (weightNumerator upper i:ℚ)
      (numerator (ratioNumerator upper i-ratioDenominator upper i)
        (ratioNumerator upper i+ratioDenominator upper i):ℚ)
      (numerator (gridNumerator upper i-2*gridDenominator) (gridNumerator upper i):ℚ)
      (denominator (ratioNumerator upper i+ratioDenominator upper i):ℚ)
      (denominator (gridNumerator upper i):ℚ) (by norm_num [gridDenominator])

theorem integer_paid_rat (upper : Bool) {i : ℕ} (hi : i < 4096) :
    (paymentNumerator upper i:ℚ)/(scale:ℚ) ≤
      rationalValue upper ((gridNumerator upper i:ℚ)/gridDenominator) := by
  simpa only [paymentNumerator,if_pos hi] using
    quotient_payment_of_exact (show 0 < scale by decide) (raw_fraction_eq upper hi)

theorem lower_paid {i : ℕ} (hi : i < 4096) :
    ClassicalSixthTableCheck.lowerCondition (paymentNumerator false) i := by
  simpa only [ClassicalSixthTableCheck.lowerCondition,scale,Nat.cast_ofNat,rationalValue,rationalRatio,
    Bool.false_eq_true,↓reduceIte,ClassicalSixthTableCheck.lowerValue,midpoint_lower] using
    integer_paid_rat false hi

theorem upper_paid {i : ℕ} (hi : i < 4096) :
    ClassicalSixthTableCheck.upperCondition (paymentNumerator true) i := by
  simpa only [ClassicalSixthTableCheck.upperCondition,scale,Nat.cast_ofNat,rationalValue,rationalRatio,
    ↓reduceIte,ClassicalSixthTableCheck.upperValue,midpoint_upper] using integer_paid_rat true hi
end WuPaper.SixthIntegerPayment
#print axioms WuPaper.SixthIntegerPayment.raw_fraction_eq
#print axioms WuPaper.SixthIntegerPayment.lower_paid
#print axioms WuPaper.SixthIntegerPayment.upper_paid
""",
    'WR2ClassicalSixthLowerRoot.lean': r"""import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthIntegerSoundness
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature

theorem all_lower_paid (i : ℕ) (hindex : i < 4096) : lowerPayment i ≤
    lowerValue ((point 2 split 4096 i+point 2 split 4096 (i+1))/2) :=
  ClassicalSixthTableCheck.lowerCondition_sound (SixthIntegerPayment.lower_paid hindex)

end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.all_lower_paid
""",
    'WR2ClassicalSixthUpperRoot.lean': r"""import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthIntegerSoundness
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature

theorem all_upper_paid (i : ℕ) (hindex : i < 4096) : upperPayment i ≤
    upperValue ((point split endpoint 4096 i+point split endpoint 4096 (i+1))/2) :=
  ClassicalSixthTableCheck.upperCondition_sound (SixthIntegerPayment.upper_paid hindex)

end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.all_upper_paid
""",
    'WR2ClassicalSixthCertificate.lean': r"""import WR2ClassicalSixthLowerRoot
import WR2ClassicalSixthUpperRoot
noncomputable section
namespace WuPaper.ClassicalSixthRational

theorem sixth_main_lower : (381909:ℝ)/100000 ≤ Wu08TerminalAlignment.sixthMain :=
  ClassicalSixthAssembly.sixth_lower_of_payments lowerPayment upperPayment
    all_lower_paid all_upper_paid lower_total upper_total

end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.sixth_main_lower
""",
}

def integer_values(upper):
    D = 168755200
    base, step = (576151552,12575) if upper else (337510400,29131)
    L = 334639305
    def log_parts(p,q):
        coeff = [L//(2*j+1) for j in range(12)]
        P,Q = p*p,q*q
        poly = coeff[-1]
        power = Q
        for c in reversed(coeff[:-1]):
            poly = poly*P+c*power
            power *= Q
        return 2*p*poly,L*q**23
    values=[]
    for i in range(4096):
        S = base+step*(2*i+1)
        U,V = 1127*D-200*S,828048*D-164800*S
        n,d = (U*V,53080000*D**2) if upper else (1327*U,V)
        assert n>=d>0
        A,C = log_parts(n-d,n+d)
        B,E = log_parts(S-2*D,S)
        values.append((10**12*1327*D**2*A*B)//(C*E*S*(1327*D-200*S)))
    return values

def generate():
    data = point_data()
    result = dict(FIXED_SOURCES)
    for tag in ['lower','upper']:
        values = integer_values(tag == 'upper')
        assert values == [p['q'] for p in data[tag]['points']]
        total = sum(values)
        title = tag.title()
        sums = f'import WR2ClassicalSixthIntegerData\nnamespace WuPaper.ClassicalSixthRational\n'
        for b in range(64):
            sums += f"""
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem {tag}_sum_block_{b:03d} :
    {tag}PaymentBlockSum {b} = {sum(values[64*b:64*(b+1)])} := by
  decide +kernel
"""
        sums += 'end WuPaper.ClassicalSixthRational\n'
        result[f'WR2ClassicalSixth{title}Sums.lean'] = sums
        rewrites = ', '.join(f'{tag}_sum_block_{b:03d}' for b in range(64))
        result[f'WR2ClassicalSixth{title}Payments.lean'] = f"""import WR2ClassicalSixth{title}Sums
import WR2ClassicalSixthAssembly
noncomputable section
namespace WuPaper.ClassicalSixthRational
open Finset

theorem {tag}_sum : (∑ i ∈ range 4096, {tag}Numerator i) = {total} := by
  rw [show 4096=64*64 by norm_num, IntegerLogHorner.sum_blocks]
  change (∑ b ∈ range 64, {tag}PaymentBlockSum b) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [{rewrites}]

theorem {tag}_total : ({total}:ℝ)/1000000000000 ≤ ∑ i ∈ range 4096, {tag}Payment i := by
  simp only [{tag}Payment,← Finset.sum_div,← Nat.cast_sum,{tag}_sum]
  rfl
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.{tag}_total
"""
    return result

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
