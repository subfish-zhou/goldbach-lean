import MathlibNt.SieveTheory.LiLiuGoldbachSharpPiecewiseLedger

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine

/-- Exact real-exponent version of the integer-power carrier test, including zero inputs. -/
theorem oneNine_power_iff_source_exponent (r q : ℕ) :
    r^10 ≤ q^9 ↔ (r : ℝ) ≤ (q : ℝ)^((19/10 : ℝ)-1) := by
  have hp : ((q : ℝ)^((19/10 : ℝ)-1))^(10 : ℝ) = (q : ℝ)^9 := by
    rw [← Real.rpow_mul (Nat.cast_nonneg q)]
    norm_num
  have he : (r : ℝ)^10 ≤ (q : ℝ)^9 ↔
      (r : ℝ) ≤ (q : ℝ)^((19/10 : ℝ)-1) := by
    rw [← Real.rpow_natCast (r : ℝ) 10, ← hp]
    exact Real.rpow_le_rpow_iff (Nat.cast_nonneg r)
      (Real.rpow_nonneg (Nat.cast_nonneg q) _) (by norm_num)
  exact_mod_cast he

/-- The actual D19 carrier is positive exactly when the paper's literal proposition holds. -/
theorem D19_pos_iff_source_oneNine (N : ℕ) :
    0 < D19 N ↔ ∃ p r q : ℕ, p ≤ N ∧ p.Prime ∧
      (r = 1 ∨ r.Prime) ∧ q.Prime ∧ N = p+r*q ∧
      (r : ℝ) ≤ (q : ℝ)^((19/10 : ℝ)-1) := by
  rw [D19_pos_iff]
  simp_rw [oneNine_power_iff_source_exponent]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine
