import WR2MotherTerms

namespace WuPaper.R2Mother

open Finset Wu2008DoubleSieve
open scoped Classical

noncomputable def eq23RHS (N : ℕ) (w u : ℝ) : ℤ :=
  2 * upsilon2 N w - (∑ p ∈ primeWindow N w u, sieveCount N p N w) -
    2 * upsilon7 N w u - lowerS3 N w u

noncomputable def eq24RHS (N : ℕ) (z w u : ℝ) : ℤ :=
  upsilon1 N z + upsilon2 N w - upsilon4 N z u +
    upsilon5 N z w + upsilon6 N z w u - 2 * upsilon7 N w u -
    upsilon9 N w u - delta1 N z w u

noncomputable def eq25RHS (N : ℕ) (z v : ℝ) : ℤ :=
  2 * upsilon1 N z - upsilon3 N z v - upsilon8 N z v + positiveS4 N z v

theorem eq23_count {N : ℕ} (hN : 0 < N) {w : ℝ} (hw : 2 ≤ w) (u : ℝ) :
    (eq23RHS N w u : ℝ) ≤
      2 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (4 * (N : ℝ) / w + 2 * (Real.sqrt N + 1)) := by
  have heq : lowerWeightRHS N w u = eq23RHS N w u + positiveS4 N w u := rfl
  have h := lowerWeightRHS_le_count_add_explicit_error hN hw u
  rw [heq, Int.cast_add] at h
  have hp := Int.cast_nonneg (R := ℝ) (positiveS4_nonneg N w u)
  linarith

theorem eq24_buchstab_balance (N : ℕ) {z w u : ℝ}
    (hzw : z ≤ w) (hwu : w ≤ u) :
    eq24RHS N z w u =
      eq23RHS N w u + lowerS3 N w u - upsilon9 N w u -
        variableS3Triples N w u := by
  have hbase := upsilon2_threefold N hzw
  have hsingle := s1_twice N u hzw
  have hsplit := sum_primeWindow_split N hzw hwu (fun p => sieveCount N p N z)
  unfold eq24RHS eq23RHS delta1 upsilon4
  omega

theorem eq24_count {N : ℕ} {κ w : ℝ} (hN : 4 ≤ N) (he : Even N)
    (hκ : 0 < κ) (hκhalf : κ ≤ 1 / 2)
    (hw : 2 ≤ (N : ℝ) ^ κ) (hwu : (N : ℝ) ^ κ ≤ w)
    {z : ℝ} (hzw : z ≤ (N : ℝ) ^ κ) :
    (eq24RHS N z ((N : ℝ) ^ κ) w : ℝ) ≤
      2 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (8 + 2 * (1 / κ) ^ 2) * (N : ℝ) ^ (1 - κ) := by
  have h23 := eq23_count (by omega : 0 < N) hw w
  have herr := lowerWeight_error_le_rpow (by omega : 0 < N) hκhalf
  have hs := lowerS3_le_variable_add_paid_error hN he hκ hw hwu
  have hbal := congrArg (fun x : ℤ => (x : ℝ)) (eq24_buchstab_balance N hzw hwu)
  push_cast at hbal
  change (lowerS3 _ _ _ : ℝ) ≤ (upsilon9 _ _ _ : ℝ) + _ + _ at hs
  nlinarith

theorem eq25_count {N : ℕ} (hN : 0 < N) {z v : ℝ}
    (hz : 2 ≤ z) (hv : 0 ≤ v) (hNv : (N : ℝ) ≤ v ^ 3) :
    (eq25RHS N z v : ℝ) ≤
      2 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (4 * (N : ℝ) / z + 2 * (Real.sqrt N + 1)) := by
  have hs := lowerS2_eq_zero_of_cubic_cutoff (z := z) hv hNv
  have h := lowerWeightRHS_le_count_add_explicit_error hN hz v
  have heq : lowerWeightRHS N z v = eq25RHS N z v := by
    unfold lowerWeightRHS eq25RHS upsilon1 upsilon3 upsilon8 positiveS4
      s3PositiveTripleTerm
    rw [hs]
    simp only [mul_zero, sub_zero, lowerS3]
  rw [heq] at h
  linarith

theorem eq24_add_eq25 (N : ℕ) (z w u v : ℝ) :
    eq24RHS N z w u + eq25RHS N z v =
      firstNine N z w u v + delta2 N z w u v := by
  unfold eq24RHS eq25RHS firstNine delta2
  ring

theorem eq26_count {N : ℕ} {κ₁ κ₂ : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hκ₁ : 1 / 18 ≤ κ₁) (hκ : κ₁ ≤ κ₂)
    (hupper : 3 * κ₁ + κ₂ ≤ 1 / 2) (hz : 2 ≤ (N : ℝ) ^ κ₁) :
    let z := (N : ℝ) ^ κ₁
    let w := (N : ℝ) ^ κ₂
    let u := (N : ℝ) ^ (1 / 2 - 3 * κ₁)
    let v := (N : ℝ) ^ (1 / 3 : ℝ)
    (firstNine N z w u v + delta2 N z w u v : ℤ) ≤
      4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) +
        (16 + 2 * (1 / κ₂) ^ 2) * (N : ℝ) ^ (1 - κ₁) := by
  dsimp only
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hzw := Real.rpow_le_rpow_of_exponent_le hN1 hκ
  have hwu := Real.rpow_le_rpow_of_exponent_le hN1
    (show κ₂ ≤ 1 / 2 - 3 * κ₁ by linarith)
  have h24 := eq24_count hN he (by linarith : 0 < κ₂)
    (by linarith : κ₂ ≤ 1 / 2) (hz.trans hzw) hwu hzw
  have hv : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := Real.rpow_nonneg hN0.le _
  have hNv : (N : ℝ) ≤ ((N : ℝ) ^ (1 / 3 : ℝ)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have h25 := eq25_count (by omega : 0 < N) hz hv hNv
  have herr := lowerWeight_error_le_rpow (by omega : 0 < N)
    (by linarith : κ₁ ≤ 1 / 2)
  have hpw := Real.rpow_le_rpow_of_exponent_le hN1
    (show 1 - κ₂ ≤ 1 - κ₁ by linarith)
  have hscale := mul_le_mul_of_nonneg_left hpw
    (show 0 ≤ 8 + 2 * (1 / κ₂) ^ 2 by positivity)
  have hjoin := congrArg (fun x : ℤ => (x : ℝ))
    (eq24_add_eq25 N ((N : ℝ) ^ κ₁) ((N : ℝ) ^ κ₂)
      ((N : ℝ) ^ (1 / 2 - 3 * κ₁)) ((N : ℝ) ^ (1 / 3 : ℝ)))
  push_cast at hjoin ⊢
  nlinarith

end WuPaper.R2Mother

#check @WuPaper.R2Mother.eq23RHS
#check @WuPaper.R2Mother.eq24RHS
#check @WuPaper.R2Mother.eq25RHS
#check @WuPaper.R2Mother.eq23_count
#check @WuPaper.R2Mother.eq24_buchstab_balance
#check @WuPaper.R2Mother.eq24_count
#check @WuPaper.R2Mother.eq25_count
#check @WuPaper.R2Mother.eq24_add_eq25
#check @WuPaper.R2Mother.eq26_count
#print axioms WuPaper.R2Mother.eq23RHS
#print axioms WuPaper.R2Mother.eq24RHS
#print axioms WuPaper.R2Mother.eq25RHS
#print axioms WuPaper.R2Mother.eq23_count
#print axioms WuPaper.R2Mother.eq24_buchstab_balance
#print axioms WuPaper.R2Mother.eq24_count
#print axioms WuPaper.R2Mother.eq25_count
#print axioms WuPaper.R2Mother.eq24_add_eq25
#print axioms WuPaper.R2Mother.eq26_count
