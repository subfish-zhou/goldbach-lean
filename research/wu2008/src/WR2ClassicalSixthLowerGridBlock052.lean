import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints052
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_052 (j : Fin 16) : lowerPayment (16*52+j.val) ≤
    lowerValue ((point 2 split 4096 (16*52+j.val)+point 2 split 4096 (16*52+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 832 ≤ lowerValue ((point 2 split 4096 832+point 2 split 4096 833)/2)
    have hp : lowerPayment 832 = (114252544223:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 832+point 2 split 4096 833)/2 = (77202703:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77202703:ℝ)/33751040)/ClassicalSixthBranch.v ((77202703:ℝ)/33751040) = (749651543099:ℝ)/380611892888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_832
  · change lowerPayment 833 ≤ lowerValue ((point 2 split 4096 833+point 2 split 4096 834)/2)
    have hp : lowerPayment 833 = (114369507337:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 833+point 2 split 4096 834)/2 = (386071777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386071777:ℝ)/168755200)/ClassicalSixthBranch.v ((386071777:ℝ)/168755200) = (29982969177:ℝ)/15222555400 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_833
  · change lowerPayment 834 ≤ lowerValue ((point 2 split 4096 834+point 2 split 4096 835)/2)
    have hp : lowerPayment 834 = (114486433087:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 834+point 2 split 4096 835)/2 = (386130039:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386130039:ℝ)/168755200)/ClassicalSixthBranch.v ((386130039:ℝ)/168755200) = (749496915751:ℝ)/380515877112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_834
  · change lowerPayment 835 ≤ lowerValue ((point 2 split 4096 835+point 2 split 4096 836)/2)
    have hp : lowerPayment 835 = (114603321506:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 835+point 2 split 4096 836)/2 = (386188301:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386188301:ℝ)/168755200)/ClassicalSixthBranch.v ((386188301:ℝ)/168755200) = (749419602077:ℝ)/380467869224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_835
  · change lowerPayment 836 ≤ lowerValue ((point 2 split 4096 836+point 2 split 4096 837)/2)
    have hp : lowerPayment 836 = (114720172629:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 836+point 2 split 4096 837)/2 = (386246563:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386246563:ℝ)/168755200)/ClassicalSixthBranch.v ((386246563:ℝ)/168755200) = (749342288403:ℝ)/380419861336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_836
  · change lowerPayment 837 ≤ lowerValue ((point 2 split 4096 837+point 2 split 4096 838)/2)
    have hp : lowerPayment 837 = (114836986488:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 837+point 2 split 4096 838)/2 = (15452193:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15452193:ℝ)/6750208)/ClassicalSixthBranch.v ((15452193:ℝ)/6750208) = (749264974729:ℝ)/380371853448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_837
  · change lowerPayment 838 ≤ lowerValue ((point 2 split 4096 838+point 2 split 4096 839)/2)
    have hp : lowerPayment 838 = (114953763117:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 838+point 2 split 4096 839)/2 = (386363087:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386363087:ℝ)/168755200)/ClassicalSixthBranch.v ((386363087:ℝ)/168755200) = (149837532211:ℝ)/76064769112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_838
  · change lowerPayment 839 ≤ lowerValue ((point 2 split 4096 839+point 2 split 4096 840)/2)
    have hp : lowerPayment 839 = (115070502550:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 839+point 2 split 4096 840)/2 = (386421349:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386421349:ℝ)/168755200)/ClassicalSixthBranch.v ((386421349:ℝ)/168755200) = (749110347381:ℝ)/380275837672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_839
  · change lowerPayment 840 ≤ lowerValue ((point 2 split 4096 840+point 2 split 4096 841)/2)
    have hp : lowerPayment 840 = (115187204821:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 840+point 2 split 4096 841)/2 = (386479611:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386479611:ℝ)/168755200)/ClassicalSixthBranch.v ((386479611:ℝ)/168755200) = (749033033707:ℝ)/380227829784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_840
  · change lowerPayment 841 ≤ lowerValue ((point 2 split 4096 841+point 2 split 4096 842)/2)
    have hp : lowerPayment 841 = (115303869962:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 841+point 2 split 4096 842)/2 = (386537873:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386537873:ℝ)/168755200)/ClassicalSixthBranch.v ((386537873:ℝ)/168755200) = (748955720033:ℝ)/380179821896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_841
  · change lowerPayment 842 ≤ lowerValue ((point 2 split 4096 842+point 2 split 4096 843)/2)
    have hp : lowerPayment 842 = (115420498008:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 842+point 2 split 4096 843)/2 = (77319227:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77319227:ℝ)/33751040)/ClassicalSixthBranch.v ((77319227:ℝ)/33751040) = (748878406359:ℝ)/380131814008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_842
  · change lowerPayment 843 ≤ lowerValue ((point 2 split 4096 843+point 2 split 4096 844)/2)
    have hp : lowerPayment 843 = (115537088991:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 843+point 2 split 4096 844)/2 = (386654397:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386654397:ℝ)/168755200)/ClassicalSixthBranch.v ((386654397:ℝ)/168755200) = (149760218537:ℝ)/76016761224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_843
  · change lowerPayment 844 ≤ lowerValue ((point 2 split 4096 844+point 2 split 4096 845)/2)
    have hp : lowerPayment 844 = (115653642946:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 844+point 2 split 4096 845)/2 = (386712659:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386712659:ℝ)/168755200)/ClassicalSixthBranch.v ((386712659:ℝ)/168755200) = (748723779011:ℝ)/380035798232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_844
  · change lowerPayment 845 ≤ lowerValue ((point 2 split 4096 845+point 2 split 4096 846)/2)
    have hp : lowerPayment 845 = (115770159905:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 845+point 2 split 4096 846)/2 = (386770921:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386770921:ℝ)/168755200)/ClassicalSixthBranch.v ((386770921:ℝ)/168755200) = (748646465337:ℝ)/379987790344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_845
  · change lowerPayment 846 ≤ lowerValue ((point 2 split 4096 846+point 2 split 4096 847)/2)
    have hp : lowerPayment 846 = (115886639903:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 846+point 2 split 4096 847)/2 = (386829183:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386829183:ℝ)/168755200)/ClassicalSixthBranch.v ((386829183:ℝ)/168755200) = (748569151663:ℝ)/379939782456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_846
  · change lowerPayment 847 ≤ lowerValue ((point 2 split 4096 847+point 2 split 4096 848)/2)
    have hp : lowerPayment 847 = (116003082972:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 847+point 2 split 4096 848)/2 = (77377489:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77377489:ℝ)/33751040)/ClassicalSixthBranch.v ((77377489:ℝ)/33751040) = (748491837989:ℝ)/379891774568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_847
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_052
