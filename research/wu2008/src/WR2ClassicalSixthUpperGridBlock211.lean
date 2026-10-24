import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints211
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_211 (j : Fin 16) : upperPayment (16*211+j.val) ≤
    upperValue ((point split endpoint 4096 (16*211+j.val)+point split endpoint 4096 (16*211+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3376 ≤ upperValue ((point split endpoint 4096 3376+point split endpoint 4096 3377)/2)
    have hp : upperPayment 3376 = (110983222149:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3376+point split endpoint 4096 3377)/2 = (661070527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661070527:ℝ)/168755200)*ClassicalSixthBranch.v ((661070527:ℝ)/168755200)/ClassicalSixthBranch.r = (86658337739025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3376
  · change upperPayment 3377 ≤ upperValue ((point split endpoint 4096 3377+point split endpoint 4096 3378)/2)
    have hp : upperPayment 3377 = (110842651080:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3377+point split endpoint 4096 3378)/2 = (661095677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661095677:ℝ)/168755200)*ClassicalSixthBranch.v ((661095677:ℝ)/168755200)/ClassicalSixthBranch.r = (86639155713305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3377
  · change upperPayment 3378 ≤ upperValue ((point split endpoint 4096 3378+point split endpoint 4096 3379)/2)
    have hp : upperPayment 3378 = (110702044266:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3378+point split endpoint 4096 3379)/2 = (661120827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661120827:ℝ)/168755200)*ClassicalSixthBranch.v ((661120827:ℝ)/168755200)/ClassicalSixthBranch.r = (86619975711657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3378
  · change upperPayment 3379 ≤ upperValue ((point split endpoint 4096 3379+point split endpoint 4096 3380)/2)
    have hp : upperPayment 3379 = (110561401697:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3379+point split endpoint 4096 3380)/2 = (661145977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661145977:ℝ)/168755200)*ClassicalSixthBranch.v ((661145977:ℝ)/168755200)/ClassicalSixthBranch.r = (86600797734081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3379
  · change upperPayment 3380 ≤ upperValue ((point split endpoint 4096 3380+point split endpoint 4096 3381)/2)
    have hp : upperPayment 3380 = (110420723364:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3380+point split endpoint 4096 3381)/2 = (661171127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661171127:ℝ)/168755200)*ClassicalSixthBranch.v ((661171127:ℝ)/168755200)/ClassicalSixthBranch.r = (86581621780577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3380
  · change upperPayment 3381 ≤ upperValue ((point split endpoint 4096 3381+point split endpoint 4096 3382)/2)
    have hp : upperPayment 3381 = (110280009258:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3381+point split endpoint 4096 3382)/2 = (661196277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661196277:ℝ)/168755200)*ClassicalSixthBranch.v ((661196277:ℝ)/168755200)/ClassicalSixthBranch.r = (86562447851145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3381
  · change upperPayment 3382 ≤ upperValue ((point split endpoint 4096 3382+point split endpoint 4096 3383)/2)
    have hp : upperPayment 3382 = (110139259371:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3382+point split endpoint 4096 3383)/2 = (661221427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661221427:ℝ)/168755200)*ClassicalSixthBranch.v ((661221427:ℝ)/168755200)/ClassicalSixthBranch.r = (86543275945785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3382
  · change upperPayment 3383 ≤ upperValue ((point split endpoint 4096 3383+point split endpoint 4096 3384)/2)
    have hp : upperPayment 3383 = (109998473693:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3383+point split endpoint 4096 3384)/2 = (661246577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661246577:ℝ)/168755200)*ClassicalSixthBranch.v ((661246577:ℝ)/168755200)/ClassicalSixthBranch.r = (86524106064497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3383
  · change upperPayment 3384 ≤ upperValue ((point split endpoint 4096 3384+point split endpoint 4096 3385)/2)
    have hp : upperPayment 3384 = (109857652215:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3384+point split endpoint 4096 3385)/2 = (661271727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661271727:ℝ)/168755200)*ClassicalSixthBranch.v ((661271727:ℝ)/168755200)/ClassicalSixthBranch.r = (86504938207281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3384
  · change upperPayment 3385 ≤ upperValue ((point split endpoint 4096 3385+point split endpoint 4096 3386)/2)
    have hp : upperPayment 3385 = (109716794928:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3385+point split endpoint 4096 3386)/2 = (661296877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661296877:ℝ)/168755200)*ClassicalSixthBranch.v ((661296877:ℝ)/168755200)/ClassicalSixthBranch.r = (86485772374137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3385
  · change upperPayment 3386 ≤ upperValue ((point split endpoint 4096 3386+point split endpoint 4096 3387)/2)
    have hp : upperPayment 3386 = (109575901824:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3386+point split endpoint 4096 3387)/2 = (661322027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661322027:ℝ)/168755200)*ClassicalSixthBranch.v ((661322027:ℝ)/168755200)/ClassicalSixthBranch.r = (86466608565065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3386
  · change upperPayment 3387 ≤ upperValue ((point split endpoint 4096 3387+point split endpoint 4096 3388)/2)
    have hp : upperPayment 3387 = (109434972892:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3387+point split endpoint 4096 3388)/2 = (661347177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661347177:ℝ)/168755200)*ClassicalSixthBranch.v ((661347177:ℝ)/168755200)/ClassicalSixthBranch.r = (86447446780065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3387
  · change upperPayment 3388 ≤ upperValue ((point split endpoint 4096 3388+point split endpoint 4096 3389)/2)
    have hp : upperPayment 3388 = (109294008124:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3388+point split endpoint 4096 3389)/2 = (661372327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661372327:ℝ)/168755200)*ClassicalSixthBranch.v ((661372327:ℝ)/168755200)/ClassicalSixthBranch.r = (86428287019137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3388
  · change upperPayment 3389 ≤ upperValue ((point split endpoint 4096 3389+point split endpoint 4096 3390)/2)
    have hp : upperPayment 3389 = (109153007511:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3389+point split endpoint 4096 3390)/2 = (661397477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661397477:ℝ)/168755200)*ClassicalSixthBranch.v ((661397477:ℝ)/168755200)/ClassicalSixthBranch.r = (86409129282281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3389
  · change upperPayment 3390 ≤ upperValue ((point split endpoint 4096 3390+point split endpoint 4096 3391)/2)
    have hp : upperPayment 3390 = (109011971044:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3390+point split endpoint 4096 3391)/2 = (661422627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661422627:ℝ)/168755200)*ClassicalSixthBranch.v ((661422627:ℝ)/168755200)/ClassicalSixthBranch.r = (86389973569497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3390
  · change upperPayment 3391 ≤ upperValue ((point split endpoint 4096 3391+point split endpoint 4096 3392)/2)
    have hp : upperPayment 3391 = (108870898713:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3391+point split endpoint 4096 3392)/2 = (661447777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((661447777:ℝ)/168755200)*ClassicalSixthBranch.v ((661447777:ℝ)/168755200)/ClassicalSixthBranch.r = (86370819880785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3391
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_211
