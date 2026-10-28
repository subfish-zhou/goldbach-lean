import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorQuantitative
import MathlibNt.SieveTheory.LiLiuGoldbachOneNineLiteralExponent

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Unconditional 1+1.9 in exact natural-power syntax. -/
theorem goldbach_onePlusOneNine_nat_unconditional :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p+r*q ∧ r^10 ≤ q^9 := by
  obtain ⟨K, hK, hk⟩ := goldbach_D19_gt_paper_0004
  refine ⟨K, hK, ?_⟩
  intro N hN hEven
  apply (D19_pos_iff N).mp
  have hseries := SingularSeries.liuSingularSeries_pos N
  have hnonneg : 0 ≤ (1 / 2500 : ℝ) *
      (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by positivity
  have hpos : (0 : ℝ) < (D19 N : ℝ) := hnonneg.trans_lt (hk N hN hEven)
  exact_mod_cast hpos

/-- Unconditional 1+1.9 in the source's real-exponent syntax.
No integral-bound or positivity premises remain. -/
theorem goldbach_onePlusOneNine_unconditional :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, Even N → ∃ p r q : ℕ,
      p ≤ N ∧ p.Prime ∧ (r = 1 ∨ r.Prime) ∧ q.Prime ∧
        N = p+r*q ∧ (r : ℝ) ≤ (q : ℝ)^((19/10 : ℝ)-1) := by
  obtain ⟨K,hK,h⟩ := goldbach_onePlusOneNine_nat_unconditional
  refine ⟨K,hK,?_⟩
  intro N hN hEven
  obtain ⟨p,r,q,hp,hpp,hr,hq,hn,hh⟩ := h N hN hEven
  exact ⟨p,r,q,hp,hpp,hr,hq,hn,(oneNine_power_iff_source_exponent r q).mp hh⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
