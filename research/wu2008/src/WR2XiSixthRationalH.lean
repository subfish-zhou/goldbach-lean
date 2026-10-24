import WR2XiSixthRationalProfile

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set MeasureTheory NodeExtension WuTarget.W01Continuous Finset
open SourceRational
open scoped Classical Interval

def logCell (a b s : ℝ) : ℝ :=
  if max a (s-1) ≤ b then log (b/max a (s-1)) else 0

theorem rationalH_exact {s : ℝ} (hs4 : s ≤ 41/10) : rationalH s =
    upperLower 2*logCell 1 (rNode 2) s+
      ∑ i ∈ Icc 3 29, upperLower i*logCell (rNode (i-1)) (rNode i) s := by
  have hc : s-1 ≤ rNode 29 := by norm_num [rNode]; linarith
  have hi (i : ℕ) : IntervalIntegrable
      ((Ioc (rNode (i-1)) (rNode i)).indicator (fun t : ℝ => upperLower i/t))
      volume (s-1) (rNode 29) :=
    (reciprocal_indicator_integrable (rNode_pos _)).intervalIntegrable
  have hiSum : IntervalIntegrable (fun t => ∑ i ∈ Icc 3 29,
      (Ioc (rNode (i-1)) (rNode i)).indicator (fun t : ℝ => upperLower i/t) t)
      volume (s-1) (rNode 29) := by
    apply Integrable.intervalIntegrable
    apply integrable_finsetSum
    intro i _
    exact reciprocal_indicator_integrable (rNode_pos _)
  unfold rationalH
  simp_rw [rationalProfile_div_expansion]
  rw [intervalIntegral.integral_add
    (reciprocal_indicator_integrable (by norm_num : (0:ℝ) < 1)).intervalIntegrable
    hiSum,
    intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  rw [indicator_reciprocal_integral (by norm_num) (rNode_mono (by omega : 2 ≤ 29)) hc]
  unfold logCell
  simp only [mul_ite,mul_zero]
  congr 1
  apply sum_congr rfl
  intro i hi'
  exact indicator_reciprocal_integral (rNode_pos _) (rNode_mono (mem_Icc.mp hi').2) hc

def lowerLogCell (a b s : ℝ) : ℝ :=
  if max a (s-1) ≤ b then SourceLogRational.lower (b/max a (s-1)) else 0

theorem lowerLogCell_bounds {a b s : ℝ} (ha : 0 < a) :
    0 ≤ lowerLogCell a b s ∧ lowerLogCell a b s ≤ logCell a b s := by
  unfold lowerLogCell logCell
  split_ifs with hab
  · have hm : 0 < max a (s-1) := ha.trans_le (le_max_left _ _)
    have hr := (one_le_div hm).mpr hab
    exact ⟨SourceLogRational.lower_nonneg hr,SourceLogRational.lower_le_log hr⟩
  · exact ⟨le_rfl,le_rfl⟩

def pointLower (s : ℝ) : ℝ :=
  upperLower 2*lowerLogCell 1 (rNode 2) s+
    ∑ i ∈ Icc 3 29, upperLower i*lowerLogCell (rNode (i-1)) (rNode i) s

theorem pointLower_nonneg (s : ℝ) : 0 ≤ pointLower s := by
  apply add_nonneg
  · exact mul_nonneg (upperLower_nonneg _) (lowerLogCell_bounds (by norm_num)).1
  · exact sum_nonneg (fun i _ => mul_nonneg (upperLower_nonneg _) (lowerLogCell_bounds (rNode_pos _)).1)

theorem pointLower_le {s : ℝ} (hs : 2 ≤ s) (hs4 : s ≤ 41/10) :
    pointLower s ≤ hContinuous RationalCandidate.lowerH s := by
  apply le_trans _ (rationalH_le hs hs4)
  rw [rationalH_exact hs4]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (lowerLogCell_bounds (by norm_num)).2 (upperLower_nonneg _)
  · exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (lowerLogCell_bounds (rNode_pos _)).2 (upperLower_nonneg _))

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.pointLower_le
