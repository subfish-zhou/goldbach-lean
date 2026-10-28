import WR2IntegerLogHorner
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
