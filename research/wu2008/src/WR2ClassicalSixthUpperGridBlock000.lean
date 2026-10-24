import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints000
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_000 (j : Fin 16) : upperPayment (16*0+j.val) ≤
    upperValue ((point split endpoint 4096 (16*0+j.val)+point split endpoint 4096 (16*0+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 0 ≤ upperValue ((point split endpoint 4096 0+point split endpoint 4096 1)/2)
    have hp : upperPayment 0 = (424278508564:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 0+point split endpoint 4096 1)/2 = (576164127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576164127:ℝ)/168755200)*ClassicalSixthBranch.v ((576164127:ℝ)/168755200)/ClassicalSixthBranch.r = (162954828020817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_0
  · change upperPayment 1 ≤ upperValue ((point split endpoint 4096 1+point split endpoint 4096 2)/2)
    have hp : upperPayment 1 = (424224424570:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1+point split endpoint 4096 2)/2 = (576189277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576189277:ℝ)/168755200)*ClassicalSixthBranch.v ((576189277:ℝ)/168755200)/ClassicalSixthBranch.r = (162928812728025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1
  · change upperPayment 2 ≤ upperValue ((point split endpoint 4096 2+point split endpoint 4096 3)/2)
    have hp : upperPayment 2 = (424170321328:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2+point split endpoint 4096 3)/2 = (576214427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576214427:ℝ)/168755200)*ClassicalSixthBranch.v ((576214427:ℝ)/168755200)/ClassicalSixthBranch.r = (162902799459305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2
  · change upperPayment 3 ≤ upperValue ((point split endpoint 4096 3+point split endpoint 4096 4)/2)
    have hp : upperPayment 3 = (424116198834:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3+point split endpoint 4096 4)/2 = (5594559:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5594559:ℝ)/1638400)*ClassicalSixthBranch.v ((5594559:ℝ)/1638400)/ClassicalSixthBranch.r = (1581328040919:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3
  · change upperPayment 4 ≤ upperValue ((point split endpoint 4096 4+point split endpoint 4096 5)/2)
    have hp : upperPayment 4 = (424062057087:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 4+point split endpoint 4096 5)/2 = (576264727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576264727:ℝ)/168755200)*ClassicalSixthBranch.v ((576264727:ℝ)/168755200)/ClassicalSixthBranch.r = (162850778994081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_4
  · change upperPayment 5 ≤ upperValue ((point split endpoint 4096 5+point split endpoint 4096 6)/2)
    have hp : upperPayment 5 = (424007896085:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 5+point split endpoint 4096 6)/2 = (576289877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576289877:ℝ)/168755200)*ClassicalSixthBranch.v ((576289877:ℝ)/168755200)/ClassicalSixthBranch.r = (162824771797577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_5
  · change upperPayment 6 ≤ upperValue ((point split endpoint 4096 6+point split endpoint 4096 7)/2)
    have hp : upperPayment 6 = (423953715825:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 6+point split endpoint 4096 7)/2 = (576315027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576315027:ℝ)/168755200)*ClassicalSixthBranch.v ((576315027:ℝ)/168755200)/ClassicalSixthBranch.r = (162798766625145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_6
  · change upperPayment 7 ≤ upperValue ((point split endpoint 4096 7+point split endpoint 4096 8)/2)
    have hp : upperPayment 7 = (423899516306:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 7+point split endpoint 4096 8)/2 = (576340177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576340177:ℝ)/168755200)*ClassicalSixthBranch.v ((576340177:ℝ)/168755200)/ClassicalSixthBranch.r = (162772763476785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_7
  · change upperPayment 8 ≤ upperValue ((point split endpoint 4096 8+point split endpoint 4096 9)/2)
    have hp : upperPayment 8 = (423845297525:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 8+point split endpoint 4096 9)/2 = (576365327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576365327:ℝ)/168755200)*ClassicalSixthBranch.v ((576365327:ℝ)/168755200)/ClassicalSixthBranch.r = (162746762352497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_8
  · change upperPayment 9 ≤ upperValue ((point split endpoint 4096 9+point split endpoint 4096 10)/2)
    have hp : upperPayment 9 = (423791059480:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 9+point split endpoint 4096 10)/2 = (576390477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576390477:ℝ)/168755200)*ClassicalSixthBranch.v ((576390477:ℝ)/168755200)/ClassicalSixthBranch.r = (162720763252281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_9
  · change upperPayment 10 ≤ upperValue ((point split endpoint 4096 10+point split endpoint 4096 11)/2)
    have hp : upperPayment 10 = (423736802169:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 10+point split endpoint 4096 11)/2 = (576415627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576415627:ℝ)/168755200)*ClassicalSixthBranch.v ((576415627:ℝ)/168755200)/ClassicalSixthBranch.r = (162694766176137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_10
  · change upperPayment 11 ≤ upperValue ((point split endpoint 4096 11+point split endpoint 4096 12)/2)
    have hp : upperPayment 11 = (423682525590:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 11+point split endpoint 4096 12)/2 = (576440777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576440777:ℝ)/168755200)*ClassicalSixthBranch.v ((576440777:ℝ)/168755200)/ClassicalSixthBranch.r = (162668771124065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_11
  · change upperPayment 12 ≤ upperValue ((point split endpoint 4096 12+point split endpoint 4096 13)/2)
    have hp : upperPayment 12 = (423628229741:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 12+point split endpoint 4096 13)/2 = (576465927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576465927:ℝ)/168755200)*ClassicalSixthBranch.v ((576465927:ℝ)/168755200)/ClassicalSixthBranch.r = (162642778096065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_12
  · change upperPayment 13 ≤ upperValue ((point split endpoint 4096 13+point split endpoint 4096 14)/2)
    have hp : upperPayment 13 = (423573914620:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 13+point split endpoint 4096 14)/2 = (576491077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576491077:ℝ)/168755200)*ClassicalSixthBranch.v ((576491077:ℝ)/168755200)/ClassicalSixthBranch.r = (162616787092137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_13
  · change upperPayment 14 ≤ upperValue ((point split endpoint 4096 14+point split endpoint 4096 15)/2)
    have hp : upperPayment 14 = (423519580224:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 14+point split endpoint 4096 15)/2 = (576516227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576516227:ℝ)/168755200)*ClassicalSixthBranch.v ((576516227:ℝ)/168755200)/ClassicalSixthBranch.r = (162590798112281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_14
  · change upperPayment 15 ≤ upperValue ((point split endpoint 4096 15+point split endpoint 4096 16)/2)
    have hp : upperPayment 15 = (423465226551:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 15+point split endpoint 4096 16)/2 = (576541377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((576541377:ℝ)/168755200)*ClassicalSixthBranch.v ((576541377:ℝ)/168755200)/ClassicalSixthBranch.r = (162564811156497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_15
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_000
