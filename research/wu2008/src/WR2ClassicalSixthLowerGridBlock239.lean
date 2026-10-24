import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints239
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_239 (j : Fin 16) : lowerPayment (16*239+j.val) ≤
    lowerValue ((point 2 split 4096 (16*239+j.val)+point 2 split 4096 (16*239+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3824 ≤ lowerValue ((point 2 split 4096 3824+point 2 split 4096 3825)/2)
    have hp : lowerPayment 3824 = (397166308070:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3824+point 2 split 4096 3825)/2 = (560333419:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560333419:ℝ)/168755200)/ClassicalSixthBranch.v ((560333419:ℝ)/168755200) = (518329030491:ℝ)/236972291992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3824
  · change lowerPayment 3825 ≤ lowerValue ((point 2 split 4096 3825+point 2 split 4096 3826)/2)
    have hp : lowerPayment 3825 = (397263705784:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3825+point 2 split 4096 3826)/2 = (560391681:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560391681:ℝ)/168755200)/ClassicalSixthBranch.v ((560391681:ℝ)/168755200) = (518251716817:ℝ)/236924284104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3825
  · change lowerPayment 3826 ≤ lowerValue ((point 2 split 4096 3826+point 2 split 4096 3827)/2)
    have hp : lowerPayment 3826 = (397361120829:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3826+point 2 split 4096 3827)/2 = (560449943:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560449943:ℝ)/168755200)/ClassicalSixthBranch.v ((560449943:ℝ)/168755200) = (518174403143:ℝ)/236876276216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3826
  · change lowerPayment 3827 ≤ lowerValue ((point 2 split 4096 3827+point 2 split 4096 3828)/2)
    have hp : lowerPayment 3827 = (397458553224:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3827+point 2 split 4096 3828)/2 = (112101641:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112101641:ℝ)/33751040)/ClassicalSixthBranch.v ((112101641:ℝ)/33751040) = (518097089469:ℝ)/236828268328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3827
  · change lowerPayment 3828 ≤ lowerValue ((point 2 split 4096 3828+point 2 split 4096 3829)/2)
    have hp : lowerPayment 3828 = (397556002986:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3828+point 2 split 4096 3829)/2 = (560566467:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560566467:ℝ)/168755200)/ClassicalSixthBranch.v ((560566467:ℝ)/168755200) = (103603955159:ℝ)/47356052088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3828
  · change lowerPayment 3829 ≤ lowerValue ((point 2 split 4096 3829+point 2 split 4096 3830)/2)
    have hp : lowerPayment 3829 = (397653470132:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3829+point 2 split 4096 3830)/2 = (560624729:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560624729:ℝ)/168755200)/ClassicalSixthBranch.v ((560624729:ℝ)/168755200) = (517942462121:ℝ)/236732252552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3829
  · change lowerPayment 3830 ≤ lowerValue ((point 2 split 4096 3830+point 2 split 4096 3831)/2)
    have hp : lowerPayment 3830 = (397750954679:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3830+point 2 split 4096 3831)/2 = (560682991:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560682991:ℝ)/168755200)/ClassicalSixthBranch.v ((560682991:ℝ)/168755200) = (517865148447:ℝ)/236684244664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3830
  · change lowerPayment 3831 ≤ lowerValue ((point 2 split 4096 3831+point 2 split 4096 3832)/2)
    have hp : lowerPayment 3831 = (397848456646:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3831+point 2 split 4096 3832)/2 = (560741253:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560741253:ℝ)/168755200)/ClassicalSixthBranch.v ((560741253:ℝ)/168755200) = (517787834773:ℝ)/236636236776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3831
  · change lowerPayment 3832 ≤ lowerValue ((point 2 split 4096 3832+point 2 split 4096 3833)/2)
    have hp : lowerPayment 3832 = (397945976050:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3832+point 2 split 4096 3833)/2 = (112159903:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112159903:ℝ)/33751040)/ClassicalSixthBranch.v ((112159903:ℝ)/33751040) = (517710521099:ℝ)/236588228888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3832
  · change lowerPayment 3833 ≤ lowerValue ((point 2 split 4096 3833+point 2 split 4096 3834)/2)
    have hp : lowerPayment 3833 = (398043512908:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3833+point 2 split 4096 3834)/2 = (560857777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560857777:ℝ)/168755200)/ClassicalSixthBranch.v ((560857777:ℝ)/168755200) = (20705328297:ℝ)/9461608840 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3833
  · change lowerPayment 3834 ≤ lowerValue ((point 2 split 4096 3834+point 2 split 4096 3835)/2)
    have hp : lowerPayment 3834 = (398141067237:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3834+point 2 split 4096 3835)/2 = (560916039:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560916039:ℝ)/168755200)/ClassicalSixthBranch.v ((560916039:ℝ)/168755200) = (517555893751:ℝ)/236492213112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3834
  · change lowerPayment 3835 ≤ lowerValue ((point 2 split 4096 3835+point 2 split 4096 3836)/2)
    have hp : lowerPayment 3835 = (398238639056:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3835+point 2 split 4096 3836)/2 = (560974301:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((560974301:ℝ)/168755200)/ClassicalSixthBranch.v ((560974301:ℝ)/168755200) = (517478580077:ℝ)/236444205224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3835
  · change lowerPayment 3836 ≤ lowerValue ((point 2 split 4096 3836+point 2 split 4096 3837)/2)
    have hp : lowerPayment 3836 = (398336228382:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3836+point 2 split 4096 3837)/2 = (561032563:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561032563:ℝ)/168755200)/ClassicalSixthBranch.v ((561032563:ℝ)/168755200) = (517401266403:ℝ)/236396197336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3836
  · change lowerPayment 3837 ≤ lowerValue ((point 2 split 4096 3837+point 2 split 4096 3838)/2)
    have hp : lowerPayment 3837 = (398433835231:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3837+point 2 split 4096 3838)/2 = (22443633:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22443633:ℝ)/6750208)/ClassicalSixthBranch.v ((22443633:ℝ)/6750208) = (517323952729:ℝ)/236348189448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3837
  · change lowerPayment 3838 ≤ lowerValue ((point 2 split 4096 3838+point 2 split 4096 3839)/2)
    have hp : lowerPayment 3838 = (398531459623:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3838+point 2 split 4096 3839)/2 = (561149087:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561149087:ℝ)/168755200)/ClassicalSixthBranch.v ((561149087:ℝ)/168755200) = (103449327811:ℝ)/47260036312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3838
  · change lowerPayment 3839 ≤ lowerValue ((point 2 split 4096 3839+point 2 split 4096 3840)/2)
    have hp : lowerPayment 3839 = (398629101573:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3839+point 2 split 4096 3840)/2 = (561207349:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((561207349:ℝ)/168755200)/ClassicalSixthBranch.v ((561207349:ℝ)/168755200) = (517169325381:ℝ)/236252173672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3839
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_239
