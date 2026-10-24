import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints249
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_249 (j : Fin 16) : upperPayment (16*249+j.val) ≤
    upperValue ((point split endpoint 4096 (16*249+j.val)+point split endpoint 4096 (16*249+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3984 ≤ upperValue ((point split endpoint 4096 3984+point split endpoint 4096 3985)/2)
    have hp : upperPayment 3984 = (18560903965:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3984+point split endpoint 4096 3985)/2 = (676361727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676361727:ℝ)/168755200)*ClassicalSixthBranch.v ((676361727:ℝ)/168755200)/ClassicalSixthBranch.r = (75369164059281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3984
  · change upperPayment 3985 ≤ upperValue ((point split endpoint 4096 3985+point split endpoint 4096 3986)/2)
    have hp : upperPayment 3985 = (18396782748:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3985+point split endpoint 4096 3986)/2 = (676386877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676386877:ℝ)/168755200)*ClassicalSixthBranch.v ((676386877:ℝ)/168755200)/ClassicalSixthBranch.r = (75351212669337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3985
  · change upperPayment 3986 ≤ upperValue ((point split endpoint 4096 3986+point split endpoint 4096 3987)/2)
    have hp : upperPayment 3986 = (18232619531:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3986+point split endpoint 4096 3987)/2 = (676412027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676412027:ℝ)/168755200)*ClassicalSixthBranch.v ((676412027:ℝ)/168755200)/ClassicalSixthBranch.r = (75333263303465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3986
  · change upperPayment 3987 ≤ upperValue ((point split endpoint 4096 3987+point split endpoint 4096 3988)/2)
    have hp : upperPayment 3987 = (18068414304:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3987+point split endpoint 4096 3988)/2 = (676437177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676437177:ℝ)/168755200)*ClassicalSixthBranch.v ((676437177:ℝ)/168755200)/ClassicalSixthBranch.r = (75315315961665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3987
  · change upperPayment 3988 ≤ upperValue ((point split endpoint 4096 3988+point split endpoint 4096 3989)/2)
    have hp : upperPayment 3988 = (17904167053:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3988+point split endpoint 4096 3989)/2 = (676462327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676462327:ℝ)/168755200)*ClassicalSixthBranch.v ((676462327:ℝ)/168755200)/ClassicalSixthBranch.r = (75297370643937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3988
  · change upperPayment 3989 ≤ upperValue ((point split endpoint 4096 3989+point split endpoint 4096 3990)/2)
    have hp : upperPayment 3989 = (17739877768:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3989+point split endpoint 4096 3990)/2 = (676487477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676487477:ℝ)/168755200)*ClassicalSixthBranch.v ((676487477:ℝ)/168755200)/ClassicalSixthBranch.r = (75279427350281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3989
  · change upperPayment 3990 ≤ upperValue ((point split endpoint 4096 3990+point split endpoint 4096 3991)/2)
    have hp : upperPayment 3990 = (17575546437:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3990+point split endpoint 4096 3991)/2 = (676512627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676512627:ℝ)/168755200)*ClassicalSixthBranch.v ((676512627:ℝ)/168755200)/ClassicalSixthBranch.r = (75261486080697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3990
  · change upperPayment 3991 ≤ upperValue ((point split endpoint 4096 3991+point split endpoint 4096 3992)/2)
    have hp : upperPayment 3991 = (17411173049:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3991+point split endpoint 4096 3992)/2 = (676537777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676537777:ℝ)/168755200)*ClassicalSixthBranch.v ((676537777:ℝ)/168755200)/ClassicalSixthBranch.r = (75243546835185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3991
  · change upperPayment 3992 ≤ upperValue ((point split endpoint 4096 3992+point split endpoint 4096 3993)/2)
    have hp : upperPayment 3992 = (17246757591:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3992+point split endpoint 4096 3993)/2 = (676562927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676562927:ℝ)/168755200)*ClassicalSixthBranch.v ((676562927:ℝ)/168755200)/ClassicalSixthBranch.r = (75225609613745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3992
  · change upperPayment 3993 ≤ upperValue ((point split endpoint 4096 3993+point split endpoint 4096 3994)/2)
    have hp : upperPayment 3993 = (17082300051:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3993+point split endpoint 4096 3994)/2 = (676588077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676588077:ℝ)/168755200)*ClassicalSixthBranch.v ((676588077:ℝ)/168755200)/ClassicalSixthBranch.r = (75207674416377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3993
  · change upperPayment 3994 ≤ upperValue ((point split endpoint 4096 3994+point split endpoint 4096 3995)/2)
    have hp : upperPayment 3994 = (16917800419:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3994+point split endpoint 4096 3995)/2 = (676613227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676613227:ℝ)/168755200)*ClassicalSixthBranch.v ((676613227:ℝ)/168755200)/ClassicalSixthBranch.r = (75189741243081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3994
  · change upperPayment 3995 ≤ upperValue ((point split endpoint 4096 3995+point split endpoint 4096 3996)/2)
    have hp : upperPayment 3995 = (16753258682:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3995+point split endpoint 4096 3996)/2 = (676638377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676638377:ℝ)/168755200)*ClassicalSixthBranch.v ((676638377:ℝ)/168755200)/ClassicalSixthBranch.r = (75171810093857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3995
  · change upperPayment 3996 ≤ upperValue ((point split endpoint 4096 3996+point split endpoint 4096 3997)/2)
    have hp : upperPayment 3996 = (16588674828:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3996+point split endpoint 4096 3997)/2 = (676663527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676663527:ℝ)/168755200)*ClassicalSixthBranch.v ((676663527:ℝ)/168755200)/ClassicalSixthBranch.r = (75153880968705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3996
  · change upperPayment 3997 ≤ upperValue ((point split endpoint 4096 3997+point split endpoint 4096 3998)/2)
    have hp : upperPayment 3997 = (16424048847:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3997+point split endpoint 4096 3998)/2 = (676688677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676688677:ℝ)/168755200)*ClassicalSixthBranch.v ((676688677:ℝ)/168755200)/ClassicalSixthBranch.r = (75135953867625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3997
  · change upperPayment 3998 ≤ upperValue ((point split endpoint 4096 3998+point split endpoint 4096 3999)/2)
    have hp : upperPayment 3998 = (16259380726:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3998+point split endpoint 4096 3999)/2 = (676713827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676713827:ℝ)/168755200)*ClassicalSixthBranch.v ((676713827:ℝ)/168755200)/ClassicalSixthBranch.r = (75118028790617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3998
  · change upperPayment 3999 ≤ upperValue ((point split endpoint 4096 3999+point split endpoint 4096 4000)/2)
    have hp : upperPayment 3999 = (16094670453:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3999+point split endpoint 4096 4000)/2 = (676738977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((676738977:ℝ)/168755200)*ClassicalSixthBranch.v ((676738977:ℝ)/168755200)/ClassicalSixthBranch.r = (75100105737681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3999
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_249
