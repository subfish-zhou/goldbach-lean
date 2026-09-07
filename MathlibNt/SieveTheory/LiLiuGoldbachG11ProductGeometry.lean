import MathlibNt.SieveTheory.LiLiuGoldbachWeightQuadruple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Product geometry for the actual four closed prime carriers of G11, including repetitions. -/
theorem goldbachG11_product_le_fourthPower
    {N r q s t : ℕ} {z b : ℝ}
    (ht : t ∈ goldbachClosedPrimes N z b)
    (hs : s ∈ goldbachClosedPrimes N z (t : ℝ))
    (hr : r ∈ goldbachClosedPrimes N z (s : ℝ))
    (hq : q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ)) :
    ((r * q * s * t : ℕ) : ℝ) ≤ b^4 := by
  have htb := (mem_goldbachClosedPrimes_iff.mp ht).2.2.2
  have hsb := ((mem_goldbachClosedPrimes_iff.mp hs).2.2.2).trans htb
  have hrb := ((mem_goldbachClosedPrimes_iff.mp hr).2.2.2).trans hsb
  have hqb := ((mem_goldbachClosedPrimes_iff.mp hq).2.2.2).trans hsb
  have hb0 : 0 ≤ b := (Nat.cast_nonneg t).trans htb
  push_cast
  calc
    (r : ℝ) * q * s * t ≤ b * b * b * b := by gcongr
    _ = b^4 := by ring

/-- The canonical G11 product stays strictly below square-root scale.
This finite geometry is not a distribution or sieve upper-bound theorem. -/
theorem goldbachG11_canonical_product_bounds
    {N r q s t : ℕ} (hN : 2 ≤ N)
    (ht : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)))
    (hs : s ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) (t : ℝ))
    (hr : r ∈ goldbachClosedPrimes N ((N : ℝ)^(4 / 53 : ℝ)) (s : ℝ))
    (hq : q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ)) :
    ((r * q * s * t : ℕ) : ℝ) ≤ (N : ℝ)^(16 / 33 : ℝ) ∧
      ((r * q * s * t : ℕ) : ℝ) < Real.sqrt (N : ℝ) := by
  have hp := goldbachG11_product_le_fourthPower ht hs hr hq
  have heq : ((N : ℝ)^(4 / 33 : ℝ))^4 = (N : ℝ)^(16 / 33 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  rw [heq] at hp
  refine ⟨hp, hp.trans_lt ?_⟩
  rw [Real.sqrt_eq_rpow]
  exact Real.rpow_lt_rpow_of_exponent_lt
    (by exact_mod_cast (show 1 < N by omega)) (by norm_num)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig