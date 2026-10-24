import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints252
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_252 (j : Fin 16) : lowerPayment (16*252+j.val) ≤
    lowerValue ((point 2 split 4096 (16*252+j.val)+point 2 split 4096 (16*252+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 4032 ≤ lowerValue ((point 2 split 4096 4032+point 2 split 4096 4033)/2)
    have hp : lowerPayment 4032 = (417824539754:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4032+point 2 split 4096 4033)/2 = (114490383:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114490383:ℝ)/33751040)/ClassicalSixthBranch.v ((114490383:ℝ)/33751040) = (502247786299:ℝ)/226986651288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4032
  · change lowerPayment 4033 ≤ lowerValue ((point 2 split 4096 4033+point 2 split 4096 4034)/2)
    have hp : lowerPayment 4033 = (417925929878:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4033+point 2 split 4096 4034)/2 = (572510177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572510177:ℝ)/168755200)/ClassicalSixthBranch.v ((572510177:ℝ)/168755200) = (20086818905:ℝ)/9077545736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4033
  · change lowerPayment 4034 ≤ lowerValue ((point 2 split 4096 4034+point 2 split 4096 4035)/2)
    have hp : lowerPayment 4034 = (418027341138:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4034+point 2 split 4096 4035)/2 = (572568439:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572568439:ℝ)/168755200)/ClassicalSixthBranch.v ((572568439:ℝ)/168755200) = (502093158951:ℝ)/226890635512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4034
  · change lowerPayment 4035 ≤ lowerValue ((point 2 split 4096 4035+point 2 split 4096 4036)/2)
    have hp : lowerPayment 4035 = (418128773554:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4035+point 2 split 4096 4036)/2 = (572626701:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572626701:ℝ)/168755200)/ClassicalSixthBranch.v ((572626701:ℝ)/168755200) = (502015845277:ℝ)/226842627624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4035
  · change lowerPayment 4036 ≤ lowerValue ((point 2 split 4096 4036+point 2 split 4096 4037)/2)
    have hp : lowerPayment 4036 = (418230227145:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4036+point 2 split 4096 4037)/2 = (572684963:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572684963:ℝ)/168755200)/ClassicalSixthBranch.v ((572684963:ℝ)/168755200) = (501938531603:ℝ)/226794619736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4036
  · change lowerPayment 4037 ≤ lowerValue ((point 2 split 4096 4037+point 2 split 4096 4038)/2)
    have hp : lowerPayment 4037 = (418331701930:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4037+point 2 split 4096 4038)/2 = (22909729:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((22909729:ℝ)/6750208)/ClassicalSixthBranch.v ((22909729:ℝ)/6750208) = (501861217929:ℝ)/226746611848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4037
  · change lowerPayment 4038 ≤ lowerValue ((point 2 split 4096 4038+point 2 split 4096 4039)/2)
    have hp : lowerPayment 4038 = (418433197928:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4038+point 2 split 4096 4039)/2 = (572801487:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572801487:ℝ)/168755200)/ClassicalSixthBranch.v ((572801487:ℝ)/168755200) = (100356780851:ℝ)/45339720792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4038
  · change lowerPayment 4039 ≤ lowerValue ((point 2 split 4096 4039+point 2 split 4096 4040)/2)
    have hp : lowerPayment 4039 = (418534715159:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4039+point 2 split 4096 4040)/2 = (572859749:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572859749:ℝ)/168755200)/ClassicalSixthBranch.v ((572859749:ℝ)/168755200) = (501706590581:ℝ)/226650596072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4039
  · change lowerPayment 4040 ≤ lowerValue ((point 2 split 4096 4040+point 2 split 4096 4041)/2)
    have hp : lowerPayment 4040 = (418636253642:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4040+point 2 split 4096 4041)/2 = (572918011:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572918011:ℝ)/168755200)/ClassicalSixthBranch.v ((572918011:ℝ)/168755200) = (501629276907:ℝ)/226602588184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4040
  · change lowerPayment 4041 ≤ lowerValue ((point 2 split 4096 4041+point 2 split 4096 4042)/2)
    have hp : lowerPayment 4041 = (418737813396:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4041+point 2 split 4096 4042)/2 = (572976273:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((572976273:ℝ)/168755200)/ClassicalSixthBranch.v ((572976273:ℝ)/168755200) = (501551963233:ℝ)/226554580296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4041
  · change lowerPayment 4042 ≤ lowerValue ((point 2 split 4096 4042+point 2 split 4096 4043)/2)
    have hp : lowerPayment 4042 = (418839394441:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4042+point 2 split 4096 4043)/2 = (114606907:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114606907:ℝ)/33751040)/ClassicalSixthBranch.v ((114606907:ℝ)/33751040) = (501474649559:ℝ)/226506572408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4042
  · change lowerPayment 4043 ≤ lowerValue ((point 2 split 4096 4043+point 2 split 4096 4044)/2)
    have hp : lowerPayment 4043 = (418940996795:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4043+point 2 split 4096 4044)/2 = (573092797:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573092797:ℝ)/168755200)/ClassicalSixthBranch.v ((573092797:ℝ)/168755200) = (100279467177:ℝ)/45291712904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4043
  · change lowerPayment 4044 ≤ lowerValue ((point 2 split 4096 4044+point 2 split 4096 4045)/2)
    have hp : lowerPayment 4044 = (419042620479:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4044+point 2 split 4096 4045)/2 = (573151059:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573151059:ℝ)/168755200)/ClassicalSixthBranch.v ((573151059:ℝ)/168755200) = (501320022211:ℝ)/226410556632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4044
  · change lowerPayment 4045 ≤ lowerValue ((point 2 split 4096 4045+point 2 split 4096 4046)/2)
    have hp : lowerPayment 4045 = (419144265511:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4045+point 2 split 4096 4046)/2 = (573209321:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573209321:ℝ)/168755200)/ClassicalSixthBranch.v ((573209321:ℝ)/168755200) = (501242708537:ℝ)/226362548744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4045
  · change lowerPayment 4046 ≤ lowerValue ((point 2 split 4096 4046+point 2 split 4096 4047)/2)
    have hp : lowerPayment 4046 = (419245931911:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4046+point 2 split 4096 4047)/2 = (573267583:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((573267583:ℝ)/168755200)/ClassicalSixthBranch.v ((573267583:ℝ)/168755200) = (501165394863:ℝ)/226314540856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4046
  · change lowerPayment 4047 ≤ lowerValue ((point 2 split 4096 4047+point 2 split 4096 4048)/2)
    have hp : lowerPayment 4047 = (419347619698:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4047+point 2 split 4096 4048)/2 = (114665169:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((114665169:ℝ)/33751040)/ClassicalSixthBranch.v ((114665169:ℝ)/33751040) = (501088081189:ℝ)/226266532968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4047
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_252
