import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints183
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_183 (j : Fin 16) : lowerPayment (16*183+j.val) ≤
    lowerValue ((point 2 split 4096 (16*183+j.val)+point 2 split 4096 (16*183+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2928 ≤ lowerValue ((point 2 split 4096 2928+point 2 split 4096 2929)/2)
    have hp : lowerPayment 2928 = (314921669125:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2928+point 2 split 4096 2929)/2 = (508130667:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((508130667:ℝ)/168755200)/ClassicalSixthBranch.v ((508130667:ℝ)/168755200) = (117520416479:ℝ)/55997471928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2928
  · change lowerPayment 2929 ≤ lowerValue ((point 2 split 4096 2929+point 2 split 4096 2930)/2)
    have hp : lowerPayment 2929 = (315009892533:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2929+point 2 split 4096 2930)/2 = (508188929:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((508188929:ℝ)/168755200)/ClassicalSixthBranch.v ((508188929:ℝ)/168755200) = (587524768721:ℝ)/279939351752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2929
  · change lowerPayment 2930 ≤ lowerValue ((point 2 split 4096 2930+point 2 split 4096 2931)/2)
    have hp : lowerPayment 2930 = (315098119592:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2930+point 2 split 4096 2931)/2 = (508247191:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((508247191:ℝ)/168755200)/ClassicalSixthBranch.v ((508247191:ℝ)/168755200) = (587447455047:ℝ)/279891343864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2930
  · change lowerPayment 2931 ≤ lowerValue ((point 2 split 4096 2931+point 2 split 4096 2932)/2)
    have hp : lowerPayment 2931 = (315186350317:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2931+point 2 split 4096 2932)/2 = (508305453:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((508305453:ℝ)/168755200)/ClassicalSixthBranch.v ((508305453:ℝ)/168755200) = (587370141373:ℝ)/279843335976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2931
  · change lowerPayment 2932 ≤ lowerValue ((point 2 split 4096 2932+point 2 split 4096 2933)/2)
    have hp : lowerPayment 2932 = (315274584721:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2932+point 2 split 4096 2933)/2 = (101672743:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101672743:ℝ)/33751040)/ClassicalSixthBranch.v ((101672743:ℝ)/33751040) = (587292827699:ℝ)/279795328088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2932
  · change lowerPayment 2933 ≤ lowerValue ((point 2 split 4096 2933+point 2 split 4096 2934)/2)
    have hp : lowerPayment 2933 = (315362822818:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2933+point 2 split 4096 2934)/2 = (508421977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((508421977:ℝ)/168755200)/ClassicalSixthBranch.v ((508421977:ℝ)/168755200) = (23488620561:ℝ)/11189892808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2933
  · change lowerPayment 2934 ≤ lowerValue ((point 2 split 4096 2934+point 2 split 4096 2935)/2)
    have hp : lowerPayment 2934 = (315451064624:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2934+point 2 split 4096 2935)/2 = (508480239:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((508480239:ℝ)/168755200)/ClassicalSixthBranch.v ((508480239:ℝ)/168755200) = (587138200351:ℝ)/279699312312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2934
  · change lowerPayment 2935 ≤ lowerValue ((point 2 split 4096 2935+point 2 split 4096 2936)/2)
    have hp : lowerPayment 2935 = (315539310151:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2935+point 2 split 4096 2936)/2 = (4937267:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4937267:ℝ)/1638400)/ClassicalSixthBranch.v ((4937267:ℝ)/1638400) = (11331253:ℝ)/5397736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2935
  · change lowerPayment 2936 ≤ lowerValue ((point 2 split 4096 2936+point 2 split 4096 2937)/2)
    have hp : lowerPayment 2936 = (315627559414:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2936+point 2 split 4096 2937)/2 = (508596763:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((508596763:ℝ)/168755200)/ClassicalSixthBranch.v ((508596763:ℝ)/168755200) = (586983573003:ℝ)/279603296536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2936
  · change lowerPayment 2937 ≤ lowerValue ((point 2 split 4096 2937+point 2 split 4096 2938)/2)
    have hp : lowerPayment 2937 = (315715812427:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2937+point 2 split 4096 2938)/2 = (20346201:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20346201:ℝ)/6750208)/ClassicalSixthBranch.v ((20346201:ℝ)/6750208) = (586906259329:ℝ)/279555288648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2937
  · change lowerPayment 2938 ≤ lowerValue ((point 2 split 4096 2938+point 2 split 4096 2939)/2)
    have hp : lowerPayment 2938 = (315804069204:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2938+point 2 split 4096 2939)/2 = (508713287:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((508713287:ℝ)/168755200)/ClassicalSixthBranch.v ((508713287:ℝ)/168755200) = (117365789131:ℝ)/55901456152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2938
  · change lowerPayment 2939 ≤ lowerValue ((point 2 split 4096 2939+point 2 split 4096 2940)/2)
    have hp : lowerPayment 2939 = (315892329760:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2939+point 2 split 4096 2940)/2 = (508771549:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((508771549:ℝ)/168755200)/ClassicalSixthBranch.v ((508771549:ℝ)/168755200) = (586751631981:ℝ)/279459272872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2939
  · change lowerPayment 2940 ≤ lowerValue ((point 2 split 4096 2940+point 2 split 4096 2941)/2)
    have hp : lowerPayment 2940 = (315980594108:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2940+point 2 split 4096 2941)/2 = (508829811:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((508829811:ℝ)/168755200)/ClassicalSixthBranch.v ((508829811:ℝ)/168755200) = (586674318307:ℝ)/279411264984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2940
  · change lowerPayment 2941 ≤ lowerValue ((point 2 split 4096 2941+point 2 split 4096 2942)/2)
    have hp : lowerPayment 2941 = (316068862262:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2941+point 2 split 4096 2942)/2 = (508888073:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((508888073:ℝ)/168755200)/ClassicalSixthBranch.v ((508888073:ℝ)/168755200) = (586597004633:ℝ)/279363257096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2941
  · change lowerPayment 2942 ≤ lowerValue ((point 2 split 4096 2942+point 2 split 4096 2943)/2)
    have hp : lowerPayment 2942 = (316157134238:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2942+point 2 split 4096 2943)/2 = (101789267:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((101789267:ℝ)/33751040)/ClassicalSixthBranch.v ((101789267:ℝ)/33751040) = (586519690959:ℝ)/279315249208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2942
  · change lowerPayment 2943 ≤ lowerValue ((point 2 split 4096 2943+point 2 split 4096 2944)/2)
    have hp : lowerPayment 2943 = (316245410048:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2943+point 2 split 4096 2944)/2 = (509004597:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((509004597:ℝ)/168755200)/ClassicalSixthBranch.v ((509004597:ℝ)/168755200) = (117288475457:ℝ)/55853448264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2943
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_183
