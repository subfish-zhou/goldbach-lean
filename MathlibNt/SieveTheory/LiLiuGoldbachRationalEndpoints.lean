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

/-- Closed and half-open prime carriers agree at these rational-power endpoints;
there is no extra endpoint error to absorb. -/
theorem goldbachClosedPrimes_eq_halfOpen_rpow
    (N a b : ℕ) (z : ℝ) (hb : 0 < b) :
    goldbachClosedPrimes N z ((N : ℝ) ^ ((a : ℝ) / (b : ℝ))) =
      goldbachHalfOpenPrimes N z ((N : ℝ) ^ ((a : ℝ) / (b : ℝ))) := by
  ext r
  rw [mem_goldbachClosedPrimes_iff, mem_goldbachHalfOpenPrimes_iff]
  constructor
  · rintro ⟨hr, hrN, hz, hy⟩
    exact ⟨hr, hrN, hz, lt_of_le_of_ne hy (goldbachPrime_ne_rpow_of_not_dvd N r a b hr hrN hb)⟩
  · rintro ⟨hr, hrN, hz, hy⟩
    exact ⟨hr, hrN, hz, hy.le⟩

theorem goldbachS3Closed_eq_halfOpen_rpow
    (A : Finset ℕ) (N a b : ℕ) (z : ℝ) (hb : 0 < b) :
    goldbachS3Closed A N z ((N : ℝ) ^ ((a : ℝ) / (b : ℝ))) =
      goldbachS3HalfOpen A N z ((N : ℝ) ^ ((a : ℝ) / (b : ℝ))) := by
  unfold goldbachS3Closed goldbachS3HalfOpen
  rw [goldbachClosedPrimes_eq_halfOpen_rpow N a b z hb]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig