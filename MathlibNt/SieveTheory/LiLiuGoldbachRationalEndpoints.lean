import MathlibNt.SieveTheory.LiLiuGoldbachClosedTriples

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- A prime at an exact nonnegative rational-power endpoint must divide N.
Thus it is absent from the Goldbach sifting prime carrier. -/
theorem goldbachPrime_ne_rpow_of_not_dvd
    (N r a b : ℕ) (hr : r.Prime) (hrN : ¬ r ∣ N) (hb : 0 < b) :
    (r : ℝ) ≠ (N : ℝ) ^ ((a : ℝ) / (b : ℝ)) := by
  intro heq
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hpowR : (r : ℝ) ^ b = (N : ℝ) ^ a := by
    rw [heq, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N),
      div_mul_cancel₀ _ hbR, Real.rpow_natCast]
  have hpow : r ^ b = N ^ a := by exact_mod_cast hpowR
  have hd : r ∣ N ^ a := by
    rw [← hpow]
    exact dvd_pow_self r hb.ne'
  exact hrN (hr.dvd_of_dvd_pow hd)


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig