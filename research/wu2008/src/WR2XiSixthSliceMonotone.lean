import WR2XiSixthContinuousGeometry

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open QuarterTrim WuSource.SrcSixthGain

/-- Each factor used in the sliced logarithmic ratio increases with the sum coordinate. -/
theorem slice_factors_mono {z w : ℝ} (h : z ≤ w) :
    upperX z ≤ upperX w ∧ z-lowerX z ≤ w-lowerX w ∧
      lowerX z ≤ lowerX w ∧ z-upperX z ≤ w-upperX w := by
  unfold upperX lowerX
  refine ⟨min_le_min le_rfl (by linarith), ?_, max_le_max le_rfl (by linarith), ?_⟩
  · simp only [max_def]
    split_ifs <;> linarith
  · simp only [min_def]
    split_ifs <;> linarith

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.slice_factors_mono
