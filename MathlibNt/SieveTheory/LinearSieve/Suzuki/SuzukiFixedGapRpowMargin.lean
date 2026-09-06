import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

/-- A fixed positive gap gives a strict power saving beyond the head-budget margin. -/
lemma fixedGap_rpow_margin
    {gap M : ℝ} (hgap0 : 0 < gap) (hgap1 : gap < 1) (hM : 4 ≤ M) :
    (1 - 1 / (M + 2)) ^ (gap / 2) < 1 - gap / (4 * M) := by
  let base : ℝ := 1 - 1 / (M + 2)
  let exponent : ℝ := gap / 2
  have hMpos : 0 < M := by linarith
  have hMp2 : 0 < M + 2 := by linarith
  have hbase0 : 0 < base := by
    dsimp [base]
    exact sub_pos.mpr ((div_lt_one hMp2).mpr (by linarith))
  have hexponent0 : 0 ≤ exponent := by dsimp [exponent]; positivity
  have hexponent1 : exponent ≤ 1 := by dsimp [exponent]; linarith
  have hamgm := Real.geom_mean_le_arith_mean2_weighted
    hexponent0 (sub_nonneg.mpr hexponent1) hbase0.le (by norm_num : (0 : ℝ) ≤ 1)
    (show exponent + (1 - exponent) = 1 by ring)
  have hlinear : base ^ exponent ≤ 1 - gap / (2 * (M + 2)) := by
    simp only [Real.one_rpow, mul_one] at hamgm
    dsimp [base, exponent] at hamgm ⊢
    convert hamgm using 1; field_simp [ne_of_gt hMp2]; ring
  have hstrict : 1 - gap / (2 * (M + 2)) < 1 - gap / (4 * M) := by
    rw [sub_lt_sub_iff_left]
    rw [div_lt_div_iff₀ (mul_pos (by norm_num) hMpos) (mul_pos (by norm_num) hMp2)]
    nlinarith
  simpa [base, exponent] using hlinear.trans_lt hstrict

end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne