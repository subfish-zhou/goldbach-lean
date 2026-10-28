import WR2ClassicalEighthRawIntegerData
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
