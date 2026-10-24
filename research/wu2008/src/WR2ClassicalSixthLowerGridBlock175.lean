import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints175
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_175 (j : Fin 16) : lowerPayment (16*175+j.val) ≤
    lowerValue ((point 2 split 4096 (16*175+j.val)+point 2 split 4096 (16*175+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2800 ≤ lowerValue ((point 2 split 4096 2800+point 2 split 4096 2801)/2)
    have hp : lowerPayment 2800 = (303654168681:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2800+point 2 split 4096 2801)/2 = (500673131:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500673131:ℝ)/168755200)/ClassicalSixthBranch.v ((500673131:ℝ)/168755200) = (597498232667:ℝ)/286132369304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2800
  · change lowerPayment 2801 ≤ lowerValue ((point 2 split 4096 2801+point 2 split 4096 2802)/2)
    have hp : lowerPayment 2801 = (303742041228:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2801+point 2 split 4096 2802)/2 = (500731393:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500731393:ℝ)/168755200)/ClassicalSixthBranch.v ((500731393:ℝ)/168755200) = (597420918993:ℝ)/286084361416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2801
  · change lowerPayment 2802 ≤ lowerValue ((point 2 split 4096 2802+point 2 split 4096 2803)/2)
    have hp : lowerPayment 2802 = (303829915621:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2802+point 2 split 4096 2803)/2 = (100157931:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100157931:ℝ)/33751040)/ClassicalSixthBranch.v ((100157931:ℝ)/33751040) = (597343605319:ℝ)/286036353528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2802
  · change lowerPayment 2803 ≤ lowerValue ((point 2 split 4096 2803+point 2 split 4096 2804)/2)
    have hp : lowerPayment 2803 = (303917791873:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2803+point 2 split 4096 2804)/2 = (500847917:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500847917:ℝ)/168755200)/ClassicalSixthBranch.v ((500847917:ℝ)/168755200) = (119453258329:ℝ)/57197669128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2803
  · change lowerPayment 2804 ≤ lowerValue ((point 2 split 4096 2804+point 2 split 4096 2805)/2)
    have hp : lowerPayment 2804 = (304005669998:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2804+point 2 split 4096 2805)/2 = (500906179:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500906179:ℝ)/168755200)/ClassicalSixthBranch.v ((500906179:ℝ)/168755200) = (597188977971:ℝ)/285940337752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2804
  · change lowerPayment 2805 ≤ lowerValue ((point 2 split 4096 2805+point 2 split 4096 2806)/2)
    have hp : lowerPayment 2805 = (304093550011:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2805+point 2 split 4096 2806)/2 = (500964441:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500964441:ℝ)/168755200)/ClassicalSixthBranch.v ((500964441:ℝ)/168755200) = (597111664297:ℝ)/285892329864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2805
  · change lowerPayment 2806 ≤ lowerValue ((point 2 split 4096 2806+point 2 split 4096 2807)/2)
    have hp : lowerPayment 2806 = (304181431926:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2806+point 2 split 4096 2807)/2 = (501022703:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501022703:ℝ)/168755200)/ClassicalSixthBranch.v ((501022703:ℝ)/168755200) = (597034350623:ℝ)/285844321976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2806
  · change lowerPayment 2807 ≤ lowerValue ((point 2 split 4096 2807+point 2 split 4096 2808)/2)
    have hp : lowerPayment 2807 = (304269315757:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2807+point 2 split 4096 2808)/2 = (100216193:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100216193:ℝ)/33751040)/ClassicalSixthBranch.v ((100216193:ℝ)/33751040) = (596957036949:ℝ)/285796314088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2807
  · change lowerPayment 2808 ≤ lowerValue ((point 2 split 4096 2808+point 2 split 4096 2809)/2)
    have hp : lowerPayment 2808 = (304357201517:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2808+point 2 split 4096 2809)/2 = (501139227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501139227:ℝ)/168755200)/ClassicalSixthBranch.v ((501139227:ℝ)/168755200) = (23875188931:ℝ)/11429932248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2808
  · change lowerPayment 2809 ≤ lowerValue ((point 2 split 4096 2809+point 2 split 4096 2810)/2)
    have hp : lowerPayment 2809 = (304445089221:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2809+point 2 split 4096 2810)/2 = (501197489:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501197489:ℝ)/168755200)/ClassicalSixthBranch.v ((501197489:ℝ)/168755200) = (596802409601:ℝ)/285700298312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2809
  · change lowerPayment 2810 ≤ lowerValue ((point 2 split 4096 2810+point 2 split 4096 2811)/2)
    have hp : lowerPayment 2810 = (304532978884:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2810+point 2 split 4096 2811)/2 = (501255751:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501255751:ℝ)/168755200)/ClassicalSixthBranch.v ((501255751:ℝ)/168755200) = (596725095927:ℝ)/285652290424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2810
  · change lowerPayment 2811 ≤ lowerValue ((point 2 split 4096 2811+point 2 split 4096 2812)/2)
    have hp : lowerPayment 2811 = (304620870519:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2811+point 2 split 4096 2812)/2 = (501314013:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501314013:ℝ)/168755200)/ClassicalSixthBranch.v ((501314013:ℝ)/168755200) = (596647782253:ℝ)/285604282536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2811
  · change lowerPayment 2812 ≤ lowerValue ((point 2 split 4096 2812+point 2 split 4096 2813)/2)
    have hp : lowerPayment 2812 = (304708764140:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2812+point 2 split 4096 2813)/2 = (20054891:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20054891:ℝ)/6750208)/ClassicalSixthBranch.v ((20054891:ℝ)/6750208) = (596570468579:ℝ)/285556274648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2812
  · change lowerPayment 2813 ≤ lowerValue ((point 2 split 4096 2813+point 2 split 4096 2814)/2)
    have hp : lowerPayment 2813 = (304796659762:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2813+point 2 split 4096 2814)/2 = (501430537:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501430537:ℝ)/168755200)/ClassicalSixthBranch.v ((501430537:ℝ)/168755200) = (119298630981:ℝ)/57101653352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2813
  · change lowerPayment 2814 ≤ lowerValue ((point 2 split 4096 2814+point 2 split 4096 2815)/2)
    have hp : lowerPayment 2814 = (304884557398:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2814+point 2 split 4096 2815)/2 = (501488799:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501488799:ℝ)/168755200)/ClassicalSixthBranch.v ((501488799:ℝ)/168755200) = (596415841231:ℝ)/285460258872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2814
  · change lowerPayment 2815 ≤ lowerValue ((point 2 split 4096 2815+point 2 split 4096 2816)/2)
    have hp : lowerPayment 2815 = (304972457063:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2815+point 2 split 4096 2816)/2 = (501547061:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501547061:ℝ)/168755200)/ClassicalSixthBranch.v ((501547061:ℝ)/168755200) = (596338527557:ℝ)/285412250984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2815
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_175
