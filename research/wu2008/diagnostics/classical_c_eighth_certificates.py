"""Generate exact integer C and eighth raw midpoint payments.

C values are audited against the fixed accepted Git table. Lean checks the
block sums and proves payment soundness by a shared integer identity.
"""
import argparse
from pathlib import Path


EIGHTH_TEMPLATES = {
    'WR2IntegerLogUpper.lean': r"""import WR2IntegerLogHorner
import WR2ClassicalCumulativeDivision
/-! Exact integer form of the existing upper logarithm, preserving its original remainder. -/
namespace WuPaper.IntegerLogUpper
open IntegerLogHorner

def hiNumerator (p q : ℕ) : ℕ :=
  numerator p q*(q^2-p^2)+2*commonDen*p^25
def hiDenominator (p q : ℕ) : ℕ := denominator q*(q^2-p^2)

theorem hiDenominator_pos {p q : ℕ} (hpq : p < q) : 0 < hiDenominator p q := by
  have hq : 0 < q := by omega
  have hs : p^2 < q^2 := Nat.pow_lt_pow_left hpq (by decide)
  have hdiff : 0 < q^2-p^2 := Nat.sub_pos_of_lt hs
  unfold hiDenominator denominator commonDen
  positivity

/-- Abstract rational identity: no grid coefficients or degree-23 substitution. -/
theorem upper_combine (A p q : ℚ) (hq : q ≠ 0) (hs : q^2-p^2 ≠ 0) :
    A/((commonDen:ℚ)*q^23)+2*(p/q)^25/(1-(p/q)^2) =
      (A*(q^2-p^2)+2*(commonDen:ℚ)*p^25)/((commonDen:ℚ)*q^23*(q^2-p^2)) := by
  have hz : 1-(p/q)^2 = (q^2-p^2)/q^2 := by
    field_simp [hq]
  rw [hz]
  norm_num only [commonDen,Nat.cast_ofNat]
  field_simp [hq,hs]
  ring

theorem logHi_nat_ratio {n d : ℕ} (hnd : d ≤ n) (hd : 0 < d) :
    ExactRational.logHi ((n:ℚ)/d) =
      (hiNumerator (n-d) (n+d):ℚ)/(hiDenominator (n-d) (n+d):ℚ) := by
  have hpq : n-d < n+d := by omega
  have hsq := Nat.pow_le_pow_left hpq.le 2
  have hspos := Nat.pow_lt_pow_left hpq (by decide : (2:ℕ) ≠ 0)
  have hdq : (d:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hq : ((n+d:ℕ):ℚ) ≠ 0 := by exact_mod_cast (show n+d ≠ 0 by omega)
  have hs : (((n+d:ℕ):ℚ)^2-((n-d:ℕ):ℚ)^2) ≠ 0 := by
    have h : ((n-d:ℕ):ℚ)^2 < ((n+d:ℕ):ℚ)^2 := by exact_mod_cast hspos
    linarith
  have hz : ((n:ℚ)/d-1)/((n:ℚ)/d+1) = ((n-d:ℕ):ℚ)/((n+d:ℕ):ℚ) := by
    rw [Nat.cast_sub hnd,Nat.cast_add]
    exact ratio_transform _ _ hdq (by simpa only [Nat.cast_add] using hq)
  rw [ExactRational.logHi,logLo_nat_ratio hnd hd,hz]
  simpa only [hiNumerator,hiDenominator,denominator,Nat.cast_add,Nat.cast_mul,
    Nat.cast_pow,Nat.cast_ofNat,Nat.cast_sub hsq] using
    upper_combine (numerator (n-d) (n+d):ℚ) ((n-d:ℕ):ℚ) ((n+d:ℕ):ℚ) hq hs

/-- Reuse the already accepted Nat ceiling inequality, then cast once. -/
theorem quotient_le_ceil (n d : ℕ) (hd : 0 < d) :
    (n:ℚ)/(d:ℚ) ≤ (ClassicalCumulativeDivision.ceilDiv n d:ℚ) := by
  have h := ClassicalCumulativeDivision.ceilDiv_paid n d hd
  have hdq : (0:ℚ) < d := by exact_mod_cast hd
  apply (div_le_iff₀ hdq).mpr
  have hh : (n:ℚ) ≤ (d:ℚ)*(ClassicalCumulativeDivision.ceilDiv n d:ℚ) := by exact_mod_cast h
  simpa only [mul_comm] using hh

theorem ceil_payment_of_exact {n d scale : ℕ} {value : ℚ}
    (hd : 0 < d) (hscale : 0 < scale) (he : (n:ℚ)/(d:ℚ) = (scale:ℚ)*value) :
    value ≤ (ClassicalCumulativeDivision.ceilDiv n d:ℚ)/(scale:ℚ) := by
  have h := div_le_div_of_nonneg_right (quotient_le_ceil n d hd) (Nat.cast_nonneg scale : (0:ℚ) ≤ scale)
  rw [he] at h
  have hs : (scale:ℚ) ≠ 0 := by exact_mod_cast hscale.ne'
  simpa only [mul_div_cancel_left₀ _ hs] using h
end WuPaper.IntegerLogUpper

#print axioms WuPaper.IntegerLogUpper.logHi_nat_ratio
#print axioms WuPaper.IntegerLogUpper.ceil_payment_of_exact
""",
    'WR2ClassicalEighthRawIntegerData.lean': r"""import Mathlib.Data.Real.Basic
import WR2IntegerLogUpper
namespace WuPaper.EighthIntegerPayment

def scale : ℕ := 1000000000000
def gridDenominator : ℕ := 16306176
def gridNumerator (i : ℕ) : ℕ := 1228800+1027*(2*i+1)
def cayleyP (i : ℕ) : ℕ := gridDenominator-3*gridNumerator i
def cayleyQ (i : ℕ) : ℕ := 3*gridDenominator-3*gridNumerator i

def rawNumerator (i : ℕ) : ℕ :=
  scale*gridDenominator^2*IntegerLogUpper.hiNumerator (cayleyP i) (cayleyQ i)
def rawDenominator (i : ℕ) : ℕ :=
  IntegerLogUpper.hiDenominator (cayleyP i) (cayleyQ i)*
    gridNumerator i*(gridDenominator-gridNumerator i)
def paymentNumerator (i : ℕ) : ℕ :=
  if i < 2048 then ClassicalCumulativeDivision.ceilDiv (rawNumerator i) (rawDenominator i) else 0
end WuPaper.EighthIntegerPayment

namespace WuPaper.ClassicalEighth
abbrev numerator := EighthIntegerPayment.paymentNumerator
noncomputable def payment (i : ℕ) : ℝ := (numerator i:ℝ)/1000000000000
def paymentBlockSum (b : ℕ) : ℕ := ∑ j ∈ Finset.range 64, numerator (64*b+j)
end WuPaper.ClassicalEighth
""",
    'WR2ClassicalEighthRawIntegerSoundness.lean': r"""import WR2ClassicalEighthRawIntegerData
import WR2ClassicalEighthTableCheck
/-! A uniform upper payment proof using the unchanged integer log formula. -/
namespace WuPaper.EighthIntegerPayment
open IntegerLogUpper

theorem grid_bounds {i : ℕ} (hi : i < 2048) :
    0 < gridNumerator i ∧ 3*gridNumerator i < gridDenominator := by
  dsimp [gridNumerator,gridDenominator]
  omega

theorem midpoint_grid (i : ℕ) :
    (gridNumerator i:ℚ)/(gridDenominator:ℚ) =
      ExactRational.midpoint (100/1327) (1/3) 2048 i := by
  simp only [gridNumerator,gridDenominator,ExactRational.midpoint,
    Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
  ring

theorem cayley_domain {i : ℕ} (hi : i < 2048) : cayleyP i < cayleyQ i := by
  have h := grid_bounds hi
  dsimp [cayleyP,cayleyQ]
  omega

theorem rawDenominator_pos {i : ℕ} (hi : i < 2048) : 0 < rawDenominator i := by
  have hg := grid_bounds hi
  have hh := hiDenominator_pos (cayley_domain hi)
  have hs : 0 < gridDenominator-gridNumerator i := by omega
  unfold rawDenominator
  exact Nat.mul_pos (Nat.mul_pos hh hg.1) hs

/-- Only a degree-two substitution; neither A nor B is expanded. -/
theorem scaled_product (K D S A B : ℚ) (hD : D ≠ 0) :
    K*D^2*A/(B*S*(D-S)) = K*((A/B)/((S/D)*(1-S/D))) := by
  have h : 1-S/D = (D-S)/D := by field_simp [hD]
  rw [h]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  field_simp [hD]

theorem raw_fraction_eq {i : ℕ} (hi : i < 2048) :
    (rawNumerator i:ℚ)/(rawDenominator i:ℚ) = (scale:ℚ)*ClassicalEighthTableCheck.value
      (ExactRational.midpoint (100/1327) (1/3) 2048 i) := by
  have hg := grid_bounds hi
  have hd : 0 < gridDenominator := by norm_num [gridDenominator]
  have hs : gridNumerator i ≤ gridDenominator := by omega
  have hn : gridDenominator ≤ 2*gridDenominator-3*gridNumerator i := by omega
  have hlog := logHi_nat_ratio hn hd
  have hp : 2*gridDenominator-3*gridNumerator i-gridDenominator = cayleyP i := by
    dsimp [cayleyP]; omega
  have hq : 2*gridDenominator-3*gridNumerator i+gridDenominator = cayleyQ i := by
    dsimp [cayleyQ]; omega
  rw [hp,hq] at hlog
  have harg : ((2*gridDenominator-3*gridNumerator i:ℕ):ℚ)/(gridDenominator:ℚ) =
      2-3*((gridNumerator i:ℚ)/gridDenominator) := by
    rw [Nat.cast_sub (show 3*gridNumerator i ≤ 2*gridDenominator by omega)]
    push_cast
    norm_num [gridDenominator]
    ring
  rw [harg] at hlog
  rw [← midpoint_grid]
  unfold ClassicalEighthTableCheck.value
  rw [hlog]
  simpa only [rawNumerator,rawDenominator,Nat.cast_mul,Nat.cast_pow,Nat.cast_sub hs] using
    scaled_product (scale:ℚ) (gridDenominator:ℚ) (gridNumerator i:ℚ)
      (hiNumerator (cayleyP i) (cayleyQ i):ℚ)
      (hiDenominator (cayleyP i) (cayleyQ i):ℚ) (by norm_num [gridDenominator])

theorem integer_paid_rat {i : ℕ} (hi : i < 2048) :
    ClassicalEighthTableCheck.value (ExactRational.midpoint (100/1327) (1/3) 2048 i) ≤
      (paymentNumerator i:ℚ)/(scale:ℚ) := by
  simpa only [paymentNumerator,if_pos hi] using
    ceil_payment_of_exact (rawDenominator_pos hi) (show 0 < scale by norm_num [scale])
      (raw_fraction_eq hi)
end WuPaper.EighthIntegerPayment

#print axioms WuPaper.EighthIntegerPayment.raw_fraction_eq
#print axioms WuPaper.EighthIntegerPayment.integer_paid_rat
""",
    'WR2ClassicalEighthRawCertificate.lean': r"""import WR2ClassicalEighthRawIntegerSoundness
noncomputable section
namespace WuPaper.ClassicalEighth
open Finset

theorem all_paid (i : ℕ) (hi : i < 2048) : upperValue ((point (i)+point ((i)+1))/2) ≤ payment (i) := by
  apply ClassicalEighthTableCheck.condition_sound
  simpa only [ClassicalEighthTableCheck.condition,EighthIntegerPayment.scale,Nat.cast_ofNat] using
    EighthIntegerPayment.integer_paid_rat hi

theorem raw_upper : 8*Wu2008DoubleSieve.SeventhEighth.J8 ≤ (52990343:ℝ)/10000000 := by
  apply (uniform_upper payment all_paid).trans
  simp only [payment,← sum_div,← Nat.cast_sum,numerator_sum]
  norm_num [point,step,lowerEndpoint,Wu2008DoubleSieve.SeventhEighth.alpha]
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.raw_upper
""",
}

def eighth_payments():
    """Preserve the original logHi remainder (no /25) and exact ceiling."""
    L,D,K = 334639305,16306176,10**12
    coeff = [L//(2*j+1) for j in range(12)]
    values=[]
    for i in range(2048):
        S=1228800+1027*(2*i+1)
        p,q=D-3*S,3*D-3*S
        assert 0<=p<q and 0<S<D
        P,Q=p*p,q*q
        H=coeff[-1]
        power=Q
        for c in reversed(coeff[:-1]):
            H=P*H+c*power
            power*=Q
        hiN=2*p*H*(Q-P)+2*L*p**25
        hiD=L*q**23*(Q-P)
        n,d=K*D**2*hiN,hiD*S*(D-S)
        values.append((n+d-1)//d)
    assert sum(values)==5258450040652036
    return values

def generate_eighth():
    result=dict(EIGHTH_TEMPLATES)
    values=eighth_payments()
    checks='import WR2ClassicalEighthRawIntegerData\nnamespace WuPaper.ClassicalEighth\n'
    for b in range(32):
        checks+=f"""
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem raw_sum_block_{b:03d} :
    paymentBlockSum {b} = {sum(values[64*b:64*(b+1)])} := by
  decide +kernel
"""
    checks+='end WuPaper.ClassicalEighth\n'
    checks+=''.join(f'#print axioms WuPaper.ClassicalEighth.raw_sum_block_{b:03d}\n' for b in range(32))
    result['WR2ClassicalEighthRawSums.lean']=checks
    rewrites=', '.join(f'raw_sum_block_{b:03d}' for b in range(32))
    result['WR2ClassicalEighthRawPayments.lean']=f"""import WR2ClassicalEighthRawSums
import WR2ClassicalEighthQuadrature
noncomputable section
namespace WuPaper.ClassicalEighth
open Finset

theorem numerator_sum : (∑ i ∈ range 2048, numerator i) = 5258450040652036 := by
  rw [show 2048=32*64 by norm_num, IntegerLogHorner.sum_blocks]
  change (∑ b ∈ range 32, paymentBlockSum b) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [{rewrites}]
end WuPaper.ClassicalEighth
#print axioms WuPaper.ClassicalEighth.numerator_sum
"""
    return result


C_TEMPLATES = {
    'WR2IntegerLogHorner.lean': r"""import WR2ExactRationalLogData
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Data.Nat.Cast.Order.Field

/-! Exact integer form of the existing twelve-term logarithm lower bound.
The only high-degree identity is proved in abstract p,q coordinates. -/
namespace WuPaper.IntegerLogHorner
open Finset

def commonDen : ℕ := 334639305

def homogeneous {R : Type*} [CommSemiring R] (p q : R) : R :=
  let P := p^2
  let Q := q^2
  334639305*Q^11+P*(111546435*Q^10+P*(66927861*Q^9+P*(47805615*Q^8+P*(37182145*Q^7+P*(30421755*Q^6+P*(25741485*Q^5+P*(22309287*Q^4+P*(19684665*Q^3+P*(17612595*Q^2+P*(15935205*Q^1+P*(14549535)))))))))))

def numerator (p q : ℕ) : ℕ := 2*p*homogeneous p q
def denominator (q : ℕ) : ℕ := commonDen*q^23

@[simp] theorem cast_homogeneous (p q : ℕ) :
    ((homogeneous p q : ℕ) : ℚ) = homogeneous (p:ℚ) (q:ℚ) := by
  simp only [homogeneous, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- Clearing the twelve odd denominators once. No n+d substitution occurs here. -/
theorem homogeneous_identity (p q : ℚ) (hq : q ≠ 0) :
    2*(∑ j ∈ range 12, (p/q)^(2*j+1)/(2*j+1:ℚ)) =
      (2*p*homogeneous p q)/((commonDen:ℚ)*q^23) := by
  norm_num [Finset.sum_range_succ,homogeneous,commonDen]
  field_simp [hq]
  ring

/-- This substitution is only a degree-two field identity. -/
theorem ratio_transform (n d : ℚ) (hd : d ≠ 0) (hs : n+d ≠ 0) :
    (n/d-1)/(n/d+1) = (n-d)/(n+d) := by
  field_simp [hd,hs]

theorem logLo_nat_ratio {n d : ℕ} (hnd : d ≤ n) (hd : 0 < d) :
    ExactRational.logLo ((n:ℚ)/d) =
      (numerator (n-d) (n+d):ℚ)/(denominator (n+d):ℚ) := by
  have hdq : (d:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsq : ((n+d:ℕ):ℚ) ≠ 0 := by exact_mod_cast (show n+d ≠ 0 by omega)
  have hs' : (n:ℚ)+d ≠ 0 := by simpa only [Nat.cast_add] using hsq
  have hz : ((n:ℚ)/d-1)/((n:ℚ)/d+1) =
      ((n-d:ℕ):ℚ)/((n+d:ℕ):ℚ) := by
    rw [Nat.cast_sub hnd,Nat.cast_add]
    exact ratio_transform _ _ hdq hs'
  unfold ExactRational.logLo
  rw [hz]
  simpa only [numerator, denominator, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    cast_homogeneous] using
    homogeneous_identity ((n-d:ℕ):ℚ) ((n+d:ℕ):ℚ) hsq

/-- The common-denominator algebra is proved before substituting 23rd powers. -/
theorem combine_denominators (A B Q R : ℚ) (hQ : Q ≠ 0) (hR : R ≠ 0) :
    A/((commonDen:ℚ)*Q)+B/((commonDen:ℚ)*R) =
      (A*R+B*Q)/((commonDen:ℚ)*Q*R) := by
  have hL : (commonDen:ℚ) ≠ 0 := by norm_num [commonDen]
  field_simp [hQ,hR,hL]

def splitRatio (t : ℚ) : ℚ :=
  ExactRational.logLo ((1+t)/2)+ExactRational.logLo (2*t/(1+t))
def splitNumerator (n d : ℕ) : ℕ :=
  numerator (n-d) (n+3*d)*(3*n+d)^23+
    numerator (n-d) (3*n+d)*(n+3*d)^23
def splitDenominator (n d : ℕ) : ℕ :=
  commonDen*(n+3*d)^23*(3*n+d)^23

/-- The two split factors share the numerator n-d in Cayley coordinates. -/
theorem splitRatio_nat {n d : ℕ} (hnd : d ≤ n) (hd : 0 < d) :
    splitRatio ((n:ℚ)/d) =
      (splitNumerator n d:ℚ)/(splitDenominator n d:ℚ) := by
  have hdq : (d:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsq : ((n+d:ℕ):ℚ) ≠ 0 := by exact_mod_cast (show n+d ≠ 0 by omega)
  have hs' : (n:ℚ)+d ≠ 0 := by simpa only [Nat.cast_add] using hsq
  have hl : (1+(n:ℚ)/d)/2 = ((n+d:ℕ):ℚ)/((2*d:ℕ):ℚ) := by
    push_cast
    field_simp [hdq]
    ring
  have hr : 2*((n:ℚ)/d)/(1+(n:ℚ)/d) = ((2*n:ℕ):ℚ)/((n+d:ℕ):ℚ) := by
    push_cast
    field_simp [hdq,hs']
    ring
  rw [splitRatio,hl,hr,
    logLo_nat_ratio (show 2*d ≤ n+d by omega) (by omega),
    logLo_nat_ratio (show n+d ≤ 2*n by omega) (by omega)]
  rw [show n+d-2*d=n-d by omega,show n+d+2*d=n+3*d by omega,
    show 2*n-(n+d)=n-d by omega,show 2*n+(n+d)=3*n+d by omega]
  have hQ : (((n+3*d:ℕ):ℚ)^23) ≠ 0 := by positivity
  have hR : (((3*n+d:ℕ):ℚ)^23) ≠ 0 := by positivity
  simpa only [denominator,splitNumerator,splitDenominator,Nat.cast_add,
    Nat.cast_mul,Nat.cast_pow] using
    combine_denominators (numerator (n-d) (n+3*d):ℚ)
      (numerator (n-d) (3*n+d):ℚ) (((n+3*d:ℕ):ℚ)^23)
      (((3*n+d:ℕ):ℚ)^23) hQ hR

/-- Nat quotient rounding is a lower bound, including the zero-denominator case. -/
theorem quotient_payment_le (n d scale : ℕ) :
    ((n/d:ℕ):ℚ)/(scale:ℚ) ≤ ((n:ℚ)/(d:ℚ))/(scale:ℚ) :=
  div_le_div_of_nonneg_right Nat.cast_div_le (Nat.cast_nonneg _)

theorem quotient_payment_of_exact {n d scale : ℕ} {value : ℚ}
    (hscale : 0 < scale) (he : (n:ℚ)/(d:ℚ) = (scale:ℚ)*value) :
    ((n/d:ℕ):ℚ)/(scale:ℚ) ≤ value := by
  have h := quotient_payment_le n d scale
  rw [he] at h
  have hs : (scale:ℚ) ≠ 0 := by exact_mod_cast hscale.ne'
  simpa only [mul_div_cancel_left₀ _ hs] using h

/-- Partition a consecutive sum into fixed-size blocks. -/
theorem sum_blocks (f : ℕ → ℕ) (n k : ℕ) :
    (∑ i ∈ range (n*k), f i) = ∑ b ∈ range n, ∑ j ∈ range k, f (k*b+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, Finset.sum_range_add, ih, Finset.sum_range_succ]
    simp only [Nat.mul_comm n k]

end WuPaper.IntegerLogHorner
#print axioms WuPaper.IntegerLogHorner.homogeneous_identity
#print axioms WuPaper.IntegerLogHorner.logLo_nat_ratio
#print axioms WuPaper.IntegerLogHorner.splitRatio_nat
#print axioms WuPaper.IntegerLogHorner.quotient_payment_of_exact
""",
    'WR2ClassicalCIntegerData.lean': r"""import Mathlib.Data.Real.Basic
import WR2IntegerLogHorner

/-! Exact integer C payments. The outside-grid value remains zero. -/
namespace WuPaper.CIntegerPayment
open IntegerLogHorner

def scale : ℕ := 1000000000000
def gridDenominator : ℕ := 1638400
def gridNumerator (i : ℕ) : ℕ := 3276800+527*(2*i+1)

def rawNumerator (i : ℕ) : ℕ :=
  scale*gridDenominator*
    splitNumerator (gridNumerator i-gridDenominator) gridDenominator*
    splitNumerator (1127*gridDenominator) (200*(gridNumerator i+gridDenominator))
def rawDenominator (i : ℕ) : ℕ :=
  gridNumerator i*
    splitDenominator (gridNumerator i-gridDenominator) gridDenominator*
    splitDenominator (1127*gridDenominator) (200*(gridNumerator i+gridDenominator))
def paymentNumerator (i : ℕ) : ℕ :=
  if i < 4096 then rawNumerator i/rawDenominator i else 0

end WuPaper.CIntegerPayment

namespace WuPaper.ClassicalC
abbrev cPaymentNumerator := CIntegerPayment.paymentNumerator
noncomputable def cPayment (i : ℕ) : ℝ := (cPaymentNumerator i:ℝ)/1000000000000
def cPaymentBlockSum (b : ℕ) : ℕ := ∑ j ∈ Finset.range 64, cPaymentNumerator (64*b+j)
end WuPaper.ClassicalC
""",
    'WR2ClassicalCIntegerSoundness.lean': r"""import WR2ClassicalCIntegerData
import WR2ClassicalCTableCheck

/-! Exact soundness bridge. All high-degree polynomial identities are
confined to IntegerLogHorner; the midpoint substitution below is low-degree. -/
set_option maxRecDepth 3000

namespace WuPaper.CIntegerPayment
open IntegerLogHorner

theorem grid_bounds {i : ℕ} (hi : i < 4096) :
    2*gridDenominator ≤ gridNumerator i ∧
      200*gridNumerator i ≤ 927*gridDenominator := by
  dsimp [gridNumerator,gridDenominator]
  omega

theorem midpoint_grid (i : ℕ) :
    (gridNumerator i:ℚ)/(gridDenominator:ℚ) =
      ExactRational.midpoint 2 (1327/200-2) 4096 i := by
  simp only [gridNumerator,gridDenominator,ExactRational.midpoint,
    Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
  ring

/-- Prove the product identity on abstract variables, before inserting powers. -/
theorem scaled_product (k d s A B C E : ℚ) :
    k*d*A*B/(s*C*E) = k*((A/C)/(s/d)*(B/E)) := by
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem raw_fraction_eq {i : ℕ} (hi : i < 4096) :
    (rawNumerator i:ℚ)/(rawDenominator i:ℚ) =
      (scale:ℚ)*ClassicalCTableCheck.value
        (ExactRational.midpoint 2 (1327/200-2) 4096 i) := by
  have hg := grid_bounds hi
  have hd : 0 < gridDenominator := by decide
  have hdq : (gridDenominator:ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hs0 : gridDenominator ≤ gridNumerator i := by omega
  have hl : gridDenominator ≤ gridNumerator i-gridDenominator := by omega
  have hr : 200*(gridNumerator i+gridDenominator) ≤ 1127*gridDenominator := by omega
  have hleft := splitRatio_nat hl hd
  have hright := splitRatio_nat hr
    (show 0 < 200*(gridNumerator i+gridDenominator) by omega)
  change ClassicalCTableCheck.splitLower
      (((gridNumerator i-gridDenominator:ℕ):ℚ)/(gridDenominator:ℚ)) = _ at hleft
  change ClassicalCTableCheck.splitLower
      (((1127*gridDenominator:ℕ):ℚ)/((200*(gridNumerator i+gridDenominator):ℕ):ℚ)) = _ at hright
  have harg1 : ((gridNumerator i-gridDenominator:ℕ):ℚ)/(gridDenominator:ℚ) =
      (gridNumerator i:ℚ)/(gridDenominator:ℚ)-1 := by
    rw [Nat.cast_sub hs0]
    norm_num only [gridDenominator,Nat.cast_ofNat]
    ring
  have harg2 : ((1127*gridDenominator:ℕ):ℚ)/
      ((200*(gridNumerator i+gridDenominator):ℕ):ℚ) =
      ((1327:ℚ)/200-1)/((gridNumerator i:ℚ)/(gridDenominator:ℚ)+1) := by
    have hsd : (gridNumerator i:ℚ)+(gridDenominator:ℚ) ≠ 0 := by
      exact_mod_cast (show gridNumerator i+gridDenominator ≠ 0 by omega)
    push_cast
    field_simp [hdq,hsd]
    ring
  rw [harg1] at hleft
  rw [harg2] at hright
  calc
    (rawNumerator i:ℚ)/(rawDenominator i:ℚ) = (scale:ℚ)*
        (((splitNumerator (gridNumerator i-gridDenominator) gridDenominator:ℚ)/
          (splitDenominator (gridNumerator i-gridDenominator) gridDenominator:ℚ))/
          ((gridNumerator i:ℚ)/(gridDenominator:ℚ))*
        ((splitNumerator (1127*gridDenominator) (200*(gridNumerator i+gridDenominator)):ℚ)/
          (splitDenominator (1127*gridDenominator) (200*(gridNumerator i+gridDenominator)):ℚ))) := by
      simpa only [rawNumerator,rawDenominator,Nat.cast_mul] using
        scaled_product (scale:ℚ) (gridDenominator:ℚ) (gridNumerator i:ℚ)
          (splitNumerator (gridNumerator i-gridDenominator) gridDenominator:ℚ)
          (splitNumerator (1127*gridDenominator) (200*(gridNumerator i+gridDenominator)):ℚ)
          (splitDenominator (gridNumerator i-gridDenominator) gridDenominator:ℚ)
          (splitDenominator (1127*gridDenominator) (200*(gridNumerator i+gridDenominator)):ℚ)
    _ = _ := by
      rw [← hleft,← hright,midpoint_grid]
      rfl

/-- Every formula-generated payment is paid, without checking its logs numerically. -/
theorem integer_paid_rat {i : ℕ} (hi : i < 4096) :
    (paymentNumerator i:ℚ)/(scale:ℚ) ≤
      ClassicalCTableCheck.value (ExactRational.midpoint 2 (1327/200-2) 4096 i) := by
  simpa only [paymentNumerator,if_pos hi] using
    quotient_payment_of_exact (show 0 < scale by decide) (raw_fraction_eq hi)

theorem integer_paid_real {i : ℕ} (hi : i < 4096) :
    (paymentNumerator i:ℝ)/1000000000000 ≤ ClassicalC.lowerKernel 1 (1327/200)
      ((ClassicalC.point (1327/200) 4096 i+ClassicalC.point (1327/200) 4096 (i+1))/2) := by
  have h := (Rat.cast_le (K:=ℝ)).mpr (integer_paid_rat hi)
  simpa [scale,ExactRational.midpoint,ClassicalC.point,ClassicalC.step,
    sub_sub,show (2:ℝ)+2=4 by norm_num] using h

end WuPaper.CIntegerPayment
#print axioms WuPaper.CIntegerPayment.raw_fraction_eq
#print axioms WuPaper.CIntegerPayment.integer_paid_real
""",
    'WR2ClassicalCCertificate.lean': r"""import WR2ClassicalCIntegerSoundness
import WR2ClassicalCPayments
import WR2ClassicalFirstBudget
noncomputable section
namespace WuPaper.ClassicalC
open Finset

theorem all_midpoints_paid (i : ℕ) (hi : i < 4096) : cPayment (i) ≤ lowerKernel 1 (1327/200)
    ((point (1327/200) 4096 (i)+point (1327/200) 4096 ((i)+1))/2) :=
  CIntegerPayment.integer_paid_real hi

theorem first_C_lower : (1336108:ℝ)/10000000 ≤ Wu08OriginalFirstSteps.C (1327/200) :=
  cPayment_total.trans (uniform_lower (by norm_num) (by norm_num) 1 4096
    (by norm_num) cPayment all_midpoints_paid)

theorem first_main_lower : (1490088:ℝ)/100000 ≤ Wu08TerminalAlignment.firstMain :=
  ClassicalFirst.first_lower_of_C first_C_lower

end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.first_C_lower
#print axioms WuPaper.ClassicalC.first_main_lower
""",
    'WR2ClassicalCTableCheck.lean': r"""import WR2ClassicalCUniform
import WR2ExactRationalLog

namespace WuPaper.ClassicalCTableCheck
open ExactRational

def splitLower (t : ℚ) : ℚ := logLo ((1+t)/2)+logLo (2*t/(1+t))
def value (u : ℚ) : ℚ := splitLower (u-1)/u*splitLower ((1327/200-1)/(u+1))

@[simp] theorem cast_splitLower (t : ℚ) :
    (splitLower t : ℝ) = ClassicalLogSplit.lower 1 (t : ℝ) := by
  simp [splitLower, ClassicalLogSplit.lower]

@[simp] theorem cast_value (u : ℚ) :
    (value u : ℝ) = ClassicalC.lowerKernel 1 (1327/200) (u : ℝ) := by
  simp [value, ClassicalC.lowerKernel]

end WuPaper.ClassicalCTableCheck
""",
    'WR2ExactRationalLogData.lean': r"""import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Pure rational definitions of the existing twelve-term log bounds and midpoint. -/
namespace WuPaper.ExactRational
open Finset

def logLo (t : ℚ) : ℚ :=
  2 * ∑ i ∈ range 12, ((t-1)/(t+1))^(2*i+1)/(2*i+1 : ℚ)

def logHi (t : ℚ) : ℚ :=
  logLo t + 2*((t-1)/(t+1))^25/(1-((t-1)/(t+1))^2)

/-- The same midpoint formula used by both existing quadrature assemblies. -/
def midpoint (a b : ℚ) (n i : ℕ) : ℚ :=
  (a+(b-a)/n*i + (a+(b-a)/n*(i+1)))/2

end WuPaper.ExactRational
""",
    'WR2ExactRationalLog.lean': r"""import WR2ExactRationalLogData
import WSrcFourEnclosureLogs

/-! Exact rational evaluation of the existing twelve-term logarithm bounds.
The cast identities preserve the real formulas, including their remainders.
Finite certificates use kernel reduction of rational inequalities. -/

namespace WuPaper.ExactRational
open Finset

@[simp] theorem cast_logLo (t : ℚ) :
    (logLo t : ℝ) = WuSource.SrcFourEnclosure.logLo (t : ℝ) := by
  simp [logLo, WuSource.SrcFourEnclosure.logLo]

@[simp] theorem cast_logHi (t : ℚ) :
    (logHi t : ℝ) = WuSource.SrcFourEnclosure.logHi (t : ℝ) := by
  simp [logHi, WuSource.SrcFourEnclosure.logHi]

end WuPaper.ExactRational
""",
}

BASELINE = 'c4e1b8d00dda9661140f95e0f03f0d5a08d636c2'

def c_payments():
    from math import lcm
    L = lcm(*range(1,24,2))
    coeff = [L//(2*j+1) for j in range(12)]
    def hom(p,q):
        P,Q=p*p,q*q
        h=coeff[-1]
        for j in range(10,-1,-1): h=coeff[j]*Q**(11-j)+P*h
        return 2*p*h,q**23
    def split(n,d):
        a,q=hom(n-d,n+3*d);b,r=hom(n-d,3*n+d)
        return a*r+b*q,L*q*r
    values=[]
    for i in range(4096):
        D=1638400;S=3276800+527*(2*i+1)
        a,c=split(S-D,D);b,e=split(1127*D,200*(S+D))
        values.append(1000000000000*D*a*b//(S*c*e))
    # Audit against the fixed accepted Git table; no duplicate literal table.
    import subprocess,re,hashlib
    repo=Path(__file__).resolve().parents[3]
    raw=subprocess.check_output(['git','show',BASELINE+':research/wu2008/src/WR2ClassicalCPayments.lean'],cwd=repo)
    assert hashlib.sha256(raw).hexdigest() == '289a63130201118189360a18610bb8f00a833bfafc202fcf480ff13087a29b83'
    original=[int(v) for v in re.findall(r'^  \| \d+ => (\d+)$',raw.decode(),re.M)]
    assert values==original and sum(values)==207693136875355
    return values

def generate():
    result=generate_eighth()
    result.update(C_TEMPLATES)
    values=c_payments()
    totals=[sum(values[64*b:64*b+64]) for b in range(64)]
    checks = 'import WR2ClassicalCIntegerData\nnamespace WuPaper.ClassicalC\n'
    for b,total in enumerate(totals):
        checks += f'''
set_option maxRecDepth 30000 in
set_option maxHeartbeats 4000000 in
theorem c_sum_block_{b:03d} :
    cPaymentBlockSum {b} = {total} := by
  decide +kernel
'''
    checks += 'end WuPaper.ClassicalC\n'
    checks += ''.join(f'#print axioms WuPaper.ClassicalC.c_sum_block_{b:03d}\n' for b in range(64))
    result['WR2ClassicalCSums.lean'] = checks
    s='import WR2ClassicalCUniform\nimport WR2ClassicalCSums\n'
    s+='''noncomputable section
namespace WuPaper.ClassicalC
open Finset

theorem cPayment_sum : (∑ i ∈ range 4096, cPaymentNumerator i) = 207693136875355 := by
  rw [show 4096=64*64 by norm_num, IntegerLogHorner.sum_blocks]
  change (∑ b ∈ range 64, cPaymentBlockSum b) = _
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
'''
    s+='  rw ['+', '.join(f'c_sum_block_{b:03d}' for b in range(64))+']\n'
    s+='''
theorem cPayment_total : (1336108:ℝ)/10000000 ≤
    step (1327/200) 4096*(∑ i ∈ range 4096, cPayment i)-
      (4096:ℝ)*8*(step (1327/200) 4096)^3/24 := by
  simp only [cPayment,← Finset.sum_div,← Nat.cast_sum,cPayment_sum]
  norm_num [step]

end WuPaper.ClassicalC
#print axioms WuPaper.ClassicalC.cPayment_total
'''
    result['WR2ClassicalCPayments.lean']=s
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', type=Path)
    mode.add_argument('--check', type=Path)
    args = parser.parse_args()
    destination = args.write or args.check
    if args.write:
        destination.mkdir(parents=True, exist_ok=True)
    outputs = generate()
    obsolete = sorted(destination.glob('WR2ClassicalCGridBlock*.lean')) + sorted(
        destination.glob('WR2ClassicalCSumBlock*.lean'))
    if args.write:
        for path in obsolete:
            path.unlink()
    elif obsolete:
        raise SystemExit(f'Obsolete generated C modules remain: {obsolete[0]}')
    for name, content in outputs.items():
        path = destination / name
        if args.write:
            path.write_text(content)
        elif not path.exists() or path.read_text() != content:
            raise SystemExit(f'Generated source differs: {path}')
    print(f'{"WROTE" if args.write else "CHECK_PASS"} {len(outputs)} modules; Lean verification is separate.')


if __name__ == '__main__':
    main()
