import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints235
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_235 (j : Fin 16) : lowerPayment (16*235+j.val) ≤
    lowerValue ((point 2 split 4096 (16*235+j.val)+point 2 split 4096 (16*235+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3760 ≤ lowerValue ((point 2 split 4096 3760+point 2 split 4096 3761)/2)
    have hp : lowerPayment 3760 = (390968112082:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3760+point 2 split 4096 3761)/2 = (556604651:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556604651:ℝ)/168755200)/ClassicalSixthBranch.v ((556604651:ℝ)/168755200) = (523277105627:ℝ)/240044796824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3760
  · change lowerPayment 3761 ≤ lowerValue ((point 2 split 4096 3761+point 2 split 4096 3762)/2)
    have hp : lowerPayment 3761 = (391064436507:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3761+point 2 split 4096 3762)/2 = (556662913:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556662913:ℝ)/168755200)/ClassicalSixthBranch.v ((556662913:ℝ)/168755200) = (523199791953:ℝ)/239996788936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3761
  · change lowerPayment 3762 ≤ lowerValue ((point 2 split 4096 3762+point 2 split 4096 3763)/2)
    have hp : lowerPayment 3762 = (391160777162:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3762+point 2 split 4096 3763)/2 = (22268847:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22268847:ℝ)/6750208)/ClassicalSixthBranch.v ((22268847:ℝ)/6750208) = (523122478279:ℝ)/239948781048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3762
  · change lowerPayment 3763 ≤ lowerValue ((point 2 split 4096 3763+point 2 split 4096 3764)/2)
    have hp : lowerPayment 3763 = (391257134065:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3763+point 2 split 4096 3764)/2 = (556779437:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556779437:ℝ)/168755200)/ClassicalSixthBranch.v ((556779437:ℝ)/168755200) = (104609032921:ℝ)/47980154632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3763
  · change lowerPayment 3764 ≤ lowerValue ((point 2 split 4096 3764+point 2 split 4096 3765)/2)
    have hp : lowerPayment 3764 = (391353507232:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3764+point 2 split 4096 3765)/2 = (556837699:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556837699:ℝ)/168755200)/ClassicalSixthBranch.v ((556837699:ℝ)/168755200) = (522967850931:ℝ)/239852765272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3764
  · change lowerPayment 3765 ≤ lowerValue ((point 2 split 4096 3765+point 2 split 4096 3766)/2)
    have hp : lowerPayment 3765 = (391449896681:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3765+point 2 split 4096 3766)/2 = (556895961:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556895961:ℝ)/168755200)/ClassicalSixthBranch.v ((556895961:ℝ)/168755200) = (522890537257:ℝ)/239804757384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3765
  · change lowerPayment 3766 ≤ lowerValue ((point 2 split 4096 3766+point 2 split 4096 3767)/2)
    have hp : lowerPayment 3766 = (391546302428:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3766+point 2 split 4096 3767)/2 = (556954223:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((556954223:ℝ)/168755200)/ClassicalSixthBranch.v ((556954223:ℝ)/168755200) = (522813223583:ℝ)/239756749496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3766
  · change lowerPayment 3767 ≤ lowerValue ((point 2 split 4096 3767+point 2 split 4096 3768)/2)
    have hp : lowerPayment 3767 = (391642724490:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3767+point 2 split 4096 3768)/2 = (111402497:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111402497:ℝ)/33751040)/ClassicalSixthBranch.v ((111402497:ℝ)/33751040) = (522735909909:ℝ)/239708741608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3767
  · change lowerPayment 3768 ≤ lowerValue ((point 2 split 4096 3768+point 2 split 4096 3769)/2)
    have hp : lowerPayment 3768 = (391739162885:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3768+point 2 split 4096 3769)/2 = (557070747:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557070747:ℝ)/168755200)/ClassicalSixthBranch.v ((557070747:ℝ)/168755200) = (104531719247:ℝ)/47932146744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3768
  · change lowerPayment 3769 ≤ lowerValue ((point 2 split 4096 3769+point 2 split 4096 3770)/2)
    have hp : lowerPayment 3769 = (391835617629:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3769+point 2 split 4096 3770)/2 = (557129009:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557129009:ℝ)/168755200)/ClassicalSixthBranch.v ((557129009:ℝ)/168755200) = (522581282561:ℝ)/239612725832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3769
  · change lowerPayment 3770 ≤ lowerValue ((point 2 split 4096 3770+point 2 split 4096 3771)/2)
    have hp : lowerPayment 3770 = (391932088740:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3770+point 2 split 4096 3771)/2 = (557187271:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557187271:ℝ)/168755200)/ClassicalSixthBranch.v ((557187271:ℝ)/168755200) = (522503968887:ℝ)/239564717944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3770
  · change lowerPayment 3771 ≤ lowerValue ((point 2 split 4096 3771+point 2 split 4096 3772)/2)
    have hp : lowerPayment 3771 = (392028576234:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3771+point 2 split 4096 3772)/2 = (557245533:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557245533:ℝ)/168755200)/ClassicalSixthBranch.v ((557245533:ℝ)/168755200) = (522426655213:ℝ)/239516710056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3771
  · change lowerPayment 3772 ≤ lowerValue ((point 2 split 4096 3772+point 2 split 4096 3773)/2)
    have hp : lowerPayment 3772 = (392125080129:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3772+point 2 split 4096 3773)/2 = (111460759:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((111460759:ℝ)/33751040)/ClassicalSixthBranch.v ((111460759:ℝ)/33751040) = (522349341539:ℝ)/239468702168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3772
  · change lowerPayment 3773 ≤ lowerValue ((point 2 split 4096 3773+point 2 split 4096 3774)/2)
    have hp : lowerPayment 3773 = (392221600442:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3773+point 2 split 4096 3774)/2 = (557362057:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557362057:ℝ)/168755200)/ClassicalSixthBranch.v ((557362057:ℝ)/168755200) = (104454405573:ℝ)/47884138856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3773
  · change lowerPayment 3774 ≤ lowerValue ((point 2 split 4096 3774+point 2 split 4096 3775)/2)
    have hp : lowerPayment 3774 = (392318137190:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3774+point 2 split 4096 3775)/2 = (557420319:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557420319:ℝ)/168755200)/ClassicalSixthBranch.v ((557420319:ℝ)/168755200) = (522194714191:ℝ)/239372686392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3774
  · change lowerPayment 3775 ≤ lowerValue ((point 2 split 4096 3775+point 2 split 4096 3776)/2)
    have hp : lowerPayment 3775 = (392414690389:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3775+point 2 split 4096 3776)/2 = (557478581:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((557478581:ℝ)/168755200)/ClassicalSixthBranch.v ((557478581:ℝ)/168755200) = (522117400517:ℝ)/239324678504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3775
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_235
