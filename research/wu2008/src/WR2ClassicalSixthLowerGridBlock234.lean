import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints234
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_234 (j : Fin 16) : lowerPayment (16*234+j.val) ≤
    lowerValue ((point 2 split 4096 (16*234+j.val)+point 2 split 4096 (16*234+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3744 ≤ lowerValue ((point 2 split 4096 3744+point 2 split 4096 3745)/2)
    have hp : lowerPayment 3744 = (389429114783:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3744+point 2 split 4096 3745)/2 = (555672459:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555672459:ℝ)/168755200)/ClassicalSixthBranch.v ((555672459:ℝ)/168755200) = (524514124411:ℝ)/240812923032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3744
  · change lowerPayment 3745 ≤ lowerValue ((point 2 split 4096 3745+point 2 split 4096 3746)/2)
    have hp : lowerPayment 3745 = (389525181826:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3745+point 2 split 4096 3746)/2 = (555730721:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555730721:ℝ)/168755200)/ClassicalSixthBranch.v ((555730721:ℝ)/168755200) = (524436810737:ℝ)/240764915144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3745
  · change lowerPayment 3746 ≤ lowerValue ((point 2 split 4096 3746+point 2 split 4096 3747)/2)
    have hp : lowerPayment 3746 = (389621264829:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3746+point 2 split 4096 3747)/2 = (555788983:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555788983:ℝ)/168755200)/ClassicalSixthBranch.v ((555788983:ℝ)/168755200) = (524359497063:ℝ)/240716907256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3746
  · change lowerPayment 3747 ≤ lowerValue ((point 2 split 4096 3747+point 2 split 4096 3748)/2)
    have hp : lowerPayment 3747 = (389717363808:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3747+point 2 split 4096 3748)/2 = (111169449:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111169449:ℝ)/33751040)/ClassicalSixthBranch.v ((111169449:ℝ)/33751040) = (524282183389:ℝ)/240668899368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3747
  · change lowerPayment 3748 ≤ lowerValue ((point 2 split 4096 3748+point 2 split 4096 3749)/2)
    have hp : lowerPayment 3748 = (389813478781:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3748+point 2 split 4096 3749)/2 = (555905507:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555905507:ℝ)/168755200)/ClassicalSixthBranch.v ((555905507:ℝ)/168755200) = (104840973943:ℝ)/48124178296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3748
  · change lowerPayment 3749 ≤ lowerValue ((point 2 split 4096 3749+point 2 split 4096 3750)/2)
    have hp : lowerPayment 3749 = (389909609763:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3749+point 2 split 4096 3750)/2 = (555963769:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((555963769:ℝ)/168755200)/ClassicalSixthBranch.v ((555963769:ℝ)/168755200) = (524127556041:ℝ)/240572883592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3749
  · change lowerPayment 3750 ≤ lowerValue ((point 2 split 4096 3750+point 2 split 4096 3751)/2)
    have hp : lowerPayment 3750 = (390005756773:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3750+point 2 split 4096 3751)/2 = (556022031:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556022031:ℝ)/168755200)/ClassicalSixthBranch.v ((556022031:ℝ)/168755200) = (524050242367:ℝ)/240524875704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3750
  · change lowerPayment 3751 ≤ lowerValue ((point 2 split 4096 3751+point 2 split 4096 3752)/2)
    have hp : lowerPayment 3751 = (390101919827:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3751+point 2 split 4096 3752)/2 = (556080293:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556080293:ℝ)/168755200)/ClassicalSixthBranch.v ((556080293:ℝ)/168755200) = (523972928693:ℝ)/240476867816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3751
  · change lowerPayment 3752 ≤ lowerValue ((point 2 split 4096 3752+point 2 split 4096 3753)/2)
    have hp : lowerPayment 3752 = (390198098941:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3752+point 2 split 4096 3753)/2 = (111227711:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111227711:ℝ)/33751040)/ClassicalSixthBranch.v ((111227711:ℝ)/33751040) = (523895615019:ℝ)/240428859928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3752
  · change lowerPayment 3753 ≤ lowerValue ((point 2 split 4096 3753+point 2 split 4096 3754)/2)
    have hp : lowerPayment 3753 = (390294294134:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3753+point 2 split 4096 3754)/2 = (556196817:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556196817:ℝ)/168755200)/ClassicalSixthBranch.v ((556196817:ℝ)/168755200) = (104763660269:ℝ)/48076170408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3753
  · change lowerPayment 3754 ≤ lowerValue ((point 2 split 4096 3754+point 2 split 4096 3755)/2)
    have hp : lowerPayment 3754 = (390390505421:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3754+point 2 split 4096 3755)/2 = (556255079:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556255079:ℝ)/168755200)/ClassicalSixthBranch.v ((556255079:ℝ)/168755200) = (523740987671:ℝ)/240332844152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3754
  · change lowerPayment 3755 ≤ lowerValue ((point 2 split 4096 3755+point 2 split 4096 3756)/2)
    have hp : lowerPayment 3755 = (390486732820:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3755+point 2 split 4096 3756)/2 = (556313341:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556313341:ℝ)/168755200)/ClassicalSixthBranch.v ((556313341:ℝ)/168755200) = (523663673997:ℝ)/240284836264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3755
  · change lowerPayment 3756 ≤ lowerValue ((point 2 split 4096 3756+point 2 split 4096 3757)/2)
    have hp : lowerPayment 3756 = (390582976347:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3756+point 2 split 4096 3757)/2 = (556371603:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556371603:ℝ)/168755200)/ClassicalSixthBranch.v ((556371603:ℝ)/168755200) = (523586360323:ℝ)/240236828376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3756
  · change lowerPayment 3757 ≤ lowerValue ((point 2 split 4096 3757+point 2 split 4096 3758)/2)
    have hp : lowerPayment 3757 = (390679236020:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3757+point 2 split 4096 3758)/2 = (111285973:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111285973:ℝ)/33751040)/ClassicalSixthBranch.v ((111285973:ℝ)/33751040) = (523509046649:ℝ)/240188820488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3757
  · change lowerPayment 3758 ≤ lowerValue ((point 2 split 4096 3758+point 2 split 4096 3759)/2)
    have hp : lowerPayment 3758 = (390775511856:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3758+point 2 split 4096 3759)/2 = (556488127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556488127:ℝ)/168755200)/ClassicalSixthBranch.v ((556488127:ℝ)/168755200) = (20937269319:ℝ)/9605632504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3758
  · change lowerPayment 3759 ≤ lowerValue ((point 2 split 4096 3759+point 2 split 4096 3760)/2)
    have hp : lowerPayment 3759 = (390871803871:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3759+point 2 split 4096 3760)/2 = (5403363:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((5403363:ℝ)/1638400)/ClassicalSixthBranch.v ((5403363:ℝ)/1638400) = (5081110867:ℝ)/2330998104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3759
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_234
