import WR2ExactRationalLogData
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
