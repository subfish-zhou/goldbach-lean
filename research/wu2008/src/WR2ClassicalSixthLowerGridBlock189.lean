import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints189
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_189 (j : Fin 16) : lowerPayment (16*189+j.val) ≤
    lowerValue ((point 2 split 4096 (16*189+j.val)+point 2 split 4096 (16*189+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3024 ≤ lowerValue ((point 2 split 4096 3024+point 2 split 4096 3025)/2)
    have hp : lowerPayment 3024 = (323409785375:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3024+point 2 split 4096 3025)/2 = (513723819:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513723819:ℝ)/168755200)/ClassicalSixthBranch.v ((513723819:ℝ)/168755200) = (580179969691:ℝ)/275378602392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3024
  · change lowerPayment 3025 ≤ lowerValue ((point 2 split 4096 3025+point 2 split 4096 3026)/2)
    have hp : lowerPayment 3025 = (323498423781:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3025+point 2 split 4096 3026)/2 = (513782081:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513782081:ℝ)/168755200)/ClassicalSixthBranch.v ((513782081:ℝ)/168755200) = (580102656017:ℝ)/275330594504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3025
  · change lowerPayment 3026 ≤ lowerValue ((point 2 split 4096 3026+point 2 split 4096 3027)/2)
    have hp : lowerPayment 3026 = (323587067196:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3026+point 2 split 4096 3027)/2 = (513840343:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513840343:ℝ)/168755200)/ClassicalSixthBranch.v ((513840343:ℝ)/168755200) = (580025342343:ℝ)/275282586616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3026
  · change lowerPayment 3027 ≤ lowerValue ((point 2 split 4096 3027+point 2 split 4096 3028)/2)
    have hp : lowerPayment 3027 = (323675715635:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3027+point 2 split 4096 3028)/2 = (102779721:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102779721:ℝ)/33751040)/ClassicalSixthBranch.v ((102779721:ℝ)/33751040) = (579948028669:ℝ)/275234578728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3027
  · change lowerPayment 3028 ≤ lowerValue ((point 2 split 4096 3028+point 2 split 4096 3029)/2)
    have hp : lowerPayment 3028 = (323764369113:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3028+point 2 split 4096 3029)/2 = (513956867:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((513956867:ℝ)/168755200)/ClassicalSixthBranch.v ((513956867:ℝ)/168755200) = (115974142999:ℝ)/55037314168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3028
  · change lowerPayment 3029 ≤ lowerValue ((point 2 split 4096 3029+point 2 split 4096 3030)/2)
    have hp : lowerPayment 3029 = (323853027644:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3029+point 2 split 4096 3030)/2 = (514015129:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514015129:ℝ)/168755200)/ClassicalSixthBranch.v ((514015129:ℝ)/168755200) = (579793401321:ℝ)/275138562952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3029
  · change lowerPayment 3030 ≤ lowerValue ((point 2 split 4096 3030+point 2 split 4096 3031)/2)
    have hp : lowerPayment 3030 = (323941691241:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3030+point 2 split 4096 3031)/2 = (514073391:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514073391:ℝ)/168755200)/ClassicalSixthBranch.v ((514073391:ℝ)/168755200) = (579716087647:ℝ)/275090555064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3030
  · change lowerPayment 3031 ≤ lowerValue ((point 2 split 4096 3031+point 2 split 4096 3032)/2)
    have hp : lowerPayment 3031 = (324030359919:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3031+point 2 split 4096 3032)/2 = (514131653:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514131653:ℝ)/168755200)/ClassicalSixthBranch.v ((514131653:ℝ)/168755200) = (579638773973:ℝ)/275042547176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3031
  · change lowerPayment 3032 ≤ lowerValue ((point 2 split 4096 3032+point 2 split 4096 3033)/2)
    have hp : lowerPayment 3032 = (324119033692:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3032+point 2 split 4096 3033)/2 = (102837983:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((102837983:ℝ)/33751040)/ClassicalSixthBranch.v ((102837983:ℝ)/33751040) = (579561460299:ℝ)/274994539288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3032
  · change lowerPayment 3033 ≤ lowerValue ((point 2 split 4096 3033+point 2 split 4096 3034)/2)
    have hp : lowerPayment 3033 = (324207712575:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3033+point 2 split 4096 3034)/2 = (514248177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514248177:ℝ)/168755200)/ClassicalSixthBranch.v ((514248177:ℝ)/168755200) = (23179365865:ℝ)/10997861256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3033
  · change lowerPayment 3034 ≤ lowerValue ((point 2 split 4096 3034+point 2 split 4096 3035)/2)
    have hp : lowerPayment 3034 = (324296396581:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3034+point 2 split 4096 3035)/2 = (514306439:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514306439:ℝ)/168755200)/ClassicalSixthBranch.v ((514306439:ℝ)/168755200) = (579406832951:ℝ)/274898523512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3034
  · change lowerPayment 3035 ≤ lowerValue ((point 2 split 4096 3035+point 2 split 4096 3036)/2)
    have hp : lowerPayment 3035 = (324385085725:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3035+point 2 split 4096 3036)/2 = (514364701:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514364701:ℝ)/168755200)/ClassicalSixthBranch.v ((514364701:ℝ)/168755200) = (579329519277:ℝ)/274850515624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3035
  · change lowerPayment 3036 ≤ lowerValue ((point 2 split 4096 3036+point 2 split 4096 3037)/2)
    have hp : lowerPayment 3036 = (324473780021:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3036+point 2 split 4096 3037)/2 = (514422963:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514422963:ℝ)/168755200)/ClassicalSixthBranch.v ((514422963:ℝ)/168755200) = (579252205603:ℝ)/274802507736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3036
  · change lowerPayment 3037 ≤ lowerValue ((point 2 split 4096 3037+point 2 split 4096 3038)/2)
    have hp : lowerPayment 3037 = (324562479483:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3037+point 2 split 4096 3038)/2 = (20579249:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20579249:ℝ)/6750208)/ClassicalSixthBranch.v ((20579249:ℝ)/6750208) = (579174891929:ℝ)/274754499848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3037
  · change lowerPayment 3038 ≤ lowerValue ((point 2 split 4096 3038+point 2 split 4096 3039)/2)
    have hp : lowerPayment 3038 = (324651184125:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3038+point 2 split 4096 3039)/2 = (4995529:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4995529:ℝ)/1638400)/ClassicalSixthBranch.v ((4995529:ℝ)/1638400) = (1124461317:ℝ)/533410664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3038
  · change lowerPayment 3039 ≤ lowerValue ((point 2 split 4096 3039+point 2 split 4096 3040)/2)
    have hp : lowerPayment 3039 = (324739893962:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3039+point 2 split 4096 3040)/2 = (514597749:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((514597749:ℝ)/168755200)/ClassicalSixthBranch.v ((514597749:ℝ)/168755200) = (579020264581:ℝ)/274658484072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3039
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_189
