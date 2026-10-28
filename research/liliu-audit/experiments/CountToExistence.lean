import Goldbach.OnePlusOneNine

open MathlibNt.SieveTheory.LiLiuOnePlusOneNine

namespace LiLiuAudit

/-- Derive the literal natural-power representation directly from the accepted count. -/
theorem existence_from_count :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ r ^ 10 ≤ q ^ 9 := by
  obtain ⟨K, hK, hk⟩ := Goldbach.one_plus_one_nine_count
  refine ⟨K, hK, ?_⟩
  intro N hN hEven
  apply (D19_pos_iff N).mp
  have hseries := MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N
  have hnonneg : 0 ≤ (1 / 2500 : ℝ) *
      (MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N * (N : ℝ) /
        Real.log (N : ℝ) ^ 2) := by positivity
  have hpos : (0 : ℝ) < (D19 N : ℝ) := hnonneg.trans_lt (hk N hN hEven)
  exact_mod_cast hpos

/-- Retain the equivalent real-exponent interface through the existing exact bridge. -/
theorem real_existence_from_count :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p + r * q ∧ (r : ℝ) ≤ (q : ℝ) ^ ((19 / 10 : ℝ) - 1) := by
  obtain ⟨K, hK, hk⟩ := existence_from_count
  refine ⟨K, hK, ?_⟩
  intro N hN hEven
  obtain ⟨p, r, q, hp, hpp, hr, hq, hsum, hpow⟩ := hk N hN hEven
  exact ⟨p, r, q, hp, hpp, hr, hq, hsum,
    (oneNine_power_iff_source_exponent r q).mp hpow⟩

#print axioms existence_from_count
#print axioms real_existence_from_count
end LiLiuAudit
