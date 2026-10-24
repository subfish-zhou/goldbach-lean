import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints245
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_245 (j : Fin 16) : lowerPayment (16*245+j.val) ≤
    lowerValue ((point 2 split 4096 (16*245+j.val)+point 2 split 4096 (16*245+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3920 ≤ lowerValue ((point 2 split 4096 3920+point 2 split 4096 3921)/2)
    have hp : lowerPayment 3920 = (406598040180:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3920+point 2 split 4096 3921)/2 = (565926571:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565926571:ℝ)/168755200)/ClassicalSixthBranch.v ((565926571:ℝ)/168755200) = (510906917787:ℝ)/232363534744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3920
  · change lowerPayment 3921 ≤ lowerValue ((point 2 split 4096 3921+point 2 split 4096 3922)/2)
    have hp : lowerPayment 3921 = (406697182410:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3921+point 2 split 4096 3922)/2 = (565984833:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((565984833:ℝ)/168755200)/ClassicalSixthBranch.v ((565984833:ℝ)/168755200) = (510829604113:ℝ)/232315526856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3921
  · change lowerPayment 3922 ≤ lowerValue ((point 2 split 4096 3922+point 2 split 4096 3923)/2)
    have hp : lowerPayment 3922 = (406796343682:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3922+point 2 split 4096 3923)/2 = (113208619:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113208619:ℝ)/33751040)/ClassicalSixthBranch.v ((113208619:ℝ)/33751040) = (510752290439:ℝ)/232267518968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3922
  · change lowerPayment 3923 ≤ lowerValue ((point 2 split 4096 3923+point 2 split 4096 3924)/2)
    have hp : lowerPayment 3923 = (406895524014:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3923+point 2 split 4096 3924)/2 = (566101357:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566101357:ℝ)/168755200)/ClassicalSixthBranch.v ((566101357:ℝ)/168755200) = (102134995353:ℝ)/46443902216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3923
  · change lowerPayment 3924 ≤ lowerValue ((point 2 split 4096 3924+point 2 split 4096 3925)/2)
    have hp : lowerPayment 3924 = (406994723425:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3924+point 2 split 4096 3925)/2 = (566159619:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566159619:ℝ)/168755200)/ClassicalSixthBranch.v ((566159619:ℝ)/168755200) = (510597663091:ℝ)/232171503192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3924
  · change lowerPayment 3925 ≤ lowerValue ((point 2 split 4096 3925+point 2 split 4096 3926)/2)
    have hp : lowerPayment 3925 = (407093941932:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3925+point 2 split 4096 3926)/2 = (566217881:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566217881:ℝ)/168755200)/ClassicalSixthBranch.v ((566217881:ℝ)/168755200) = (510520349417:ℝ)/232123495304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3925
  · change lowerPayment 3926 ≤ lowerValue ((point 2 split 4096 3926+point 2 split 4096 3927)/2)
    have hp : lowerPayment 3926 = (407193179555:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3926+point 2 split 4096 3927)/2 = (566276143:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566276143:ℝ)/168755200)/ClassicalSixthBranch.v ((566276143:ℝ)/168755200) = (510443035743:ℝ)/232075487416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3926
  · change lowerPayment 3927 ≤ lowerValue ((point 2 split 4096 3927+point 2 split 4096 3928)/2)
    have hp : lowerPayment 3927 = (407292436310:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3927+point 2 split 4096 3928)/2 = (113266881:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113266881:ℝ)/33751040)/ClassicalSixthBranch.v ((113266881:ℝ)/33751040) = (510365722069:ℝ)/232027479528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3927
  · change lowerPayment 3928 ≤ lowerValue ((point 2 split 4096 3928+point 2 split 4096 3929)/2)
    have hp : lowerPayment 3928 = (407391712218:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3928+point 2 split 4096 3929)/2 = (566392667:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566392667:ℝ)/168755200)/ClassicalSixthBranch.v ((566392667:ℝ)/168755200) = (102057681679:ℝ)/46395894328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3928
  · change lowerPayment 3929 ≤ lowerValue ((point 2 split 4096 3929+point 2 split 4096 3930)/2)
    have hp : lowerPayment 3929 = (407491007295:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3929+point 2 split 4096 3930)/2 = (566450929:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566450929:ℝ)/168755200)/ClassicalSixthBranch.v ((566450929:ℝ)/168755200) = (510211094721:ℝ)/231931463752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3929
  · change lowerPayment 3930 ≤ lowerValue ((point 2 split 4096 3930+point 2 split 4096 3931)/2)
    have hp : lowerPayment 3930 = (407590321560:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3930+point 2 split 4096 3931)/2 = (566509191:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566509191:ℝ)/168755200)/ClassicalSixthBranch.v ((566509191:ℝ)/168755200) = (510133781047:ℝ)/231883455864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3930
  · change lowerPayment 3931 ≤ lowerValue ((point 2 split 4096 3931+point 2 split 4096 3932)/2)
    have hp : lowerPayment 3931 = (407689655031:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3931+point 2 split 4096 3932)/2 = (566567453:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566567453:ℝ)/168755200)/ClassicalSixthBranch.v ((566567453:ℝ)/168755200) = (510056467373:ℝ)/231835447976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3931
  · change lowerPayment 3932 ≤ lowerValue ((point 2 split 4096 3932+point 2 split 4096 3933)/2)
    have hp : lowerPayment 3932 = (407789007728:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3932+point 2 split 4096 3933)/2 = (113325143:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((113325143:ℝ)/33751040)/ClassicalSixthBranch.v ((113325143:ℝ)/33751040) = (509979153699:ℝ)/231787440088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3932
  · change lowerPayment 3933 ≤ lowerValue ((point 2 split 4096 3933+point 2 split 4096 3934)/2)
    have hp : lowerPayment 3933 = (407888379667:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3933+point 2 split 4096 3934)/2 = (566683977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566683977:ℝ)/168755200)/ClassicalSixthBranch.v ((566683977:ℝ)/168755200) = (20396073601:ℝ)/9269577288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3933
  · change lowerPayment 3934 ≤ lowerValue ((point 2 split 4096 3934+point 2 split 4096 3935)/2)
    have hp : lowerPayment 3934 = (407987770867:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3934+point 2 split 4096 3935)/2 = (566742239:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566742239:ℝ)/168755200)/ClassicalSixthBranch.v ((566742239:ℝ)/168755200) = (509824526351:ℝ)/231691424312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3934
  · change lowerPayment 3935 ≤ lowerValue ((point 2 split 4096 3935+point 2 split 4096 3936)/2)
    have hp : lowerPayment 3935 = (408087181346:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3935+point 2 split 4096 3936)/2 = (566800501:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((566800501:ℝ)/168755200)/ClassicalSixthBranch.v ((566800501:ℝ)/168755200) = (509747212677:ℝ)/231643416424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3935
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_245
