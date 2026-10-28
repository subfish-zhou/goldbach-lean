import WR2ClassicalCIntegerData
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
