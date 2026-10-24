import WR2ClassicalFifthKernel
import WE07FifthSourceCover

noncomputable section
namespace WuPaper.ClassicalFifthSource
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
open ClassicalFifthKernel
open WuTarget.Wu08FifthSource

abbrev lo : ℝ := WuSource.SrcSixthGain.split
abbrev cut : ℝ := WuSource.SrcSixthGain.endpoint
abbrev hi : ℝ := ClassicalFifthBranch.endpoint

theorem source_constants : s0 = lo ∧ geometricSplit = cut ∧ FifthClassicalShape.q = hi := by
  norm_num [s0,geometricSplit,FifthClassicalShape.q,lo,cut,hi,
    WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,ClassicalFifthBranch.endpoint,
    ClassicalSixthBranch.R,a,b,QuarterTrim.alpha,QuarterTrim.beta,
    truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem geometry : (3:ℝ) ≤ lo ∧ lo ≤ 4 ∧ (4:ℝ) ≤ cut ∧ cut ≤ hi ∧ hi ≤ 5 ∧ hi ≤ ClassicalFourth.R-1 := by
  norm_num [lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
    ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,ClassicalFourth.R,QuarterTrim.alpha,QuarterTrim.beta]

private theorem den_nonzero {s : ℝ} (hs : s ≤ hi) : ClassicalFourth.R-s ≠ 0 := by
  have h := hs.trans geometry.2.2.2.2.2
  linarith

private theorem lower_ratio {s : ℝ} (hs : s ≤ cut) :
    b/(1/2-a*s-b) = ClassicalSixthBranch.r*1/ClassicalSixthBranch.v s := by
  have hv : ClassicalSixthBranch.v s ≠ 0 := by linarith [(ClassicalSixthBranch.geometry hs).2]
  have hd : 1/2-a*s-b = a*ClassicalSixthBranch.v s := by
    norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,
      ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    ring
  rw [hd]
  norm_num [a,b,truncatedSixthLowerAlpha,truncatedSixthLowerBeta,ClassicalSixthBranch.r]
  field_simp [hv]
  norm_num

private theorem upper_ratio (s : ℝ) :
    (1/2-a*s-a)/a = ClassicalSixthBranch.u s := by
  norm_num [a,truncatedSixthLowerAlpha,ClassicalSixthBranch.u,ClassicalSixthBranch.R]
  ring

theorem source_lower_literal {s : ℝ} (hs : lo ≤ s) (he : s ≤ cut) :
    scalarReduced s = kernel wuLowerCoefficient ClassicalFifthBranch.lower s := by
  have hs0 : s0 ≤ s := by rw [source_constants.1]; exact hs
  have hsQ : s ≤ FifthClassicalShape.q := by rw [source_constants.2.2]; exact he.trans geometry.2.2.2.1
  have hcut : s ≤ geometricSplit := by rw [source_constants.2.1]; exact he
  rw [scalar_reduced_literal ⟨hs0,hsQ⟩,if_pos hcut]
  unfold lowerBranch
  rw [paper_a_eq hs0 hsQ,lower_ratio he]
  unfold kernel ClassicalFifthKernel.inner ClassicalFifthBranch.lower
  rw [ClassicalFourth.weight_literal (by linarith [geometry.1] : s ≠ 0)
    (den_nonzero (he.trans geometry.2.2.2.1))]
  simp only [a,truncatedSixthLowerAlpha,div_eq_mul_inv,mul_inv_rev]
  ring

theorem source_upper_literal {s : ℝ} (hs : cut ≤ s) (he : s ≤ hi) :
    scalarReduced s = kernel wuLowerCoefficient ClassicalFifthBranch.upper s := by
  have hza : 1/2-a*s-b ≤ a := by
    norm_num [cut,WuSource.SrcSixthGain.endpoint,a,b,QuarterTrim.alpha,QuarterTrim.beta,
      truncatedSixthLowerAlpha,truncatedSixthLowerBeta] at hs ⊢
    linarith
  unfold scalarReduced sliceLower
  rw [max_eq_left hza,upper_ratio]
  unfold kernel ClassicalFifthKernel.inner ClassicalFifthBranch.upper
  rw [ClassicalFourth.weight_literal (by linarith [geometry.1,geometry.2.1,geometry.2.2.1] : s ≠ 0)
    (den_nonzero he)]
  simp only [a,truncatedSixthLowerAlpha,div_eq_mul_inv,mul_inv_rev]
  ring

theorem kernel_mono {A L : ℝ → ℝ} {s : ℝ} (hs : lo ≤ s) (he : s ≤ hi)
    (hA : A s ≤ wuLowerCoefficient s) (hL : 0 ≤ L s) :
    kernel A L s ≤ kernel wuLowerCoefficient L s := by
  have hs0 : 0 < s := by linarith [geometry.1]
  have hr0 : 0 < ClassicalFourth.R-s := by linarith [he.trans geometry.2.2.2.2.2]
  have hw : 0 ≤ ClassicalFourth.weight s := by unfold ClassicalFourth.weight; positivity
  exact mul_le_mul_of_nonneg_right hA (mul_nonneg hL hw)

theorem initial_le_source {s : ℝ} (hs : lo ≤ s) (he : s ≤ 4) :
    kernel ClassicalFifthProfile.initial ClassicalFifthBranch.lower s ≤ scalarReduced s := by
  rw [source_lower_literal hs (he.trans geometry.2.2.1)]
  apply kernel_mono hs (he.trans (geometry.2.2.1.trans geometry.2.2.2.1))
    (ClassicalFifthProfile.initial_le_lower (by linarith [geometry.1]) (by linarith))
  exact (ClassicalFifthBranch.lower_bounds hs (he.trans geometry.2.2.1)).1

theorem middle_le_source {s : ℝ} (hs : 4 ≤ s) (he : s ≤ cut) :
    kernel ClassicalFifthProfile.terminal ClassicalFifthBranch.lower s ≤ scalarReduced s := by
  rw [source_lower_literal (geometry.2.1.trans hs) he]
  apply kernel_mono (geometry.2.1.trans hs) (he.trans geometry.2.2.2.1)
    (ClassicalFifthProfile.terminal_le_lower hs (he.trans (geometry.2.2.2.1.trans geometry.2.2.2.2.1)))
  exact (ClassicalFifthBranch.lower_bounds (geometry.2.1.trans hs) he).1

theorem terminal_le_source {s : ℝ} (hs : cut ≤ s) (he : s ≤ hi) :
    kernel ClassicalFifthProfile.terminal ClassicalFifthBranch.upper s ≤ scalarReduced s := by
  rw [source_upper_literal hs he]
  apply kernel_mono (geometry.2.1.trans (geometry.2.2.1.trans hs)) he
    (ClassicalFifthProfile.terminal_le_lower (geometry.2.2.1.trans hs) (he.trans geometry.2.2.2.2.1))
  exact (ClassicalFifthBranch.upper_bounds hs he).1

end WuPaper.ClassicalFifthSource
#print axioms WuPaper.ClassicalFifthSource.source_lower_literal
#print axioms WuPaper.ClassicalFifthSource.source_upper_literal
#print axioms WuPaper.ClassicalFifthSource.terminal_le_source
