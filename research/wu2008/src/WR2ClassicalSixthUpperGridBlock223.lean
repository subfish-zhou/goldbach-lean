import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints223
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_223 (j : Fin 16) : upperPayment (16*223+j.val) ≤
    upperValue ((point split endpoint 4096 (16*223+j.val)+point split endpoint 4096 (16*223+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3568 ≤ upperValue ((point split endpoint 4096 3568+point split endpoint 4096 3569)/2)
    have hp : upperPayment 3568 = (83327446980:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3568+point split endpoint 4096 3569)/2 = (665899327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665899327:ℝ)/168755200)*ClassicalSixthBranch.v ((665899327:ℝ)/168755200)/ClassicalSixthBranch.r = (83012502184977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3568
  · change upperPayment 3569 ≤ upperValue ((point split endpoint 4096 3569+point split endpoint 4096 3570)/2)
    have hp : upperPayment 3569 = (83179842688:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3569+point split endpoint 4096 3570)/2 = (665924477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665924477:ℝ)/168755200)*ClassicalSixthBranch.v ((665924477:ℝ)/168755200)/ClassicalSixthBranch.r = (82993708781081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3569
  · change upperPayment 3570 ≤ upperValue ((point split endpoint 4096 3570+point split endpoint 4096 3571)/2)
    have hp : upperPayment 3570 = (83032200845:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3570+point split endpoint 4096 3571)/2 = (665949627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665949627:ℝ)/168755200)*ClassicalSixthBranch.v ((665949627:ℝ)/168755200)/ClassicalSixthBranch.r = (82974917401257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3570
  · change upperPayment 3571 ≤ upperValue ((point split endpoint 4096 3571+point split endpoint 4096 3572)/2)
    have hp : upperPayment 3571 = (82884521442:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3571+point split endpoint 4096 3572)/2 = (665974777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665974777:ℝ)/168755200)*ClassicalSixthBranch.v ((665974777:ℝ)/168755200)/ClassicalSixthBranch.r = (82956128045505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3571
  · change upperPayment 3572 ≤ upperValue ((point split endpoint 4096 3572+point split endpoint 4096 3573)/2)
    have hp : upperPayment 3572 = (82736804469:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3572+point split endpoint 4096 3573)/2 = (665999927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665999927:ℝ)/168755200)*ClassicalSixthBranch.v ((665999927:ℝ)/168755200)/ClassicalSixthBranch.r = (82937340713825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3572
  · change upperPayment 3573 ≤ upperValue ((point split endpoint 4096 3573+point split endpoint 4096 3574)/2)
    have hp : upperPayment 3573 = (82589049915:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3573+point split endpoint 4096 3574)/2 = (666025077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666025077:ℝ)/168755200)*ClassicalSixthBranch.v ((666025077:ℝ)/168755200)/ClassicalSixthBranch.r = (82918555406217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3573
  · change upperPayment 3574 ≤ upperValue ((point split endpoint 4096 3574+point split endpoint 4096 3575)/2)
    have hp : upperPayment 3574 = (82441257772:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3574+point split endpoint 4096 3575)/2 = (666050227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666050227:ℝ)/168755200)*ClassicalSixthBranch.v ((666050227:ℝ)/168755200)/ClassicalSixthBranch.r = (82899772122681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3574
  · change upperPayment 3575 ≤ upperValue ((point split endpoint 4096 3575+point split endpoint 4096 3576)/2)
    have hp : upperPayment 3575 = (82293428030:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3575+point split endpoint 4096 3576)/2 = (666075377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666075377:ℝ)/168755200)*ClassicalSixthBranch.v ((666075377:ℝ)/168755200)/ClassicalSixthBranch.r = (82880990863217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3575
  · change upperPayment 3576 ≤ upperValue ((point split endpoint 4096 3576+point split endpoint 4096 3577)/2)
    have hp : upperPayment 3576 = (82145560678:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3576+point split endpoint 4096 3577)/2 = (666100527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666100527:ℝ)/168755200)*ClassicalSixthBranch.v ((666100527:ℝ)/168755200)/ClassicalSixthBranch.r = (82862211627825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3576
  · change upperPayment 3577 ≤ upperValue ((point split endpoint 4096 3577+point split endpoint 4096 3578)/2)
    have hp : upperPayment 3577 = (81997655707:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3577+point split endpoint 4096 3578)/2 = (666125677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666125677:ℝ)/168755200)*ClassicalSixthBranch.v ((666125677:ℝ)/168755200)/ClassicalSixthBranch.r = (82843434416505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3577
  · change upperPayment 3578 ≤ upperValue ((point split endpoint 4096 3578+point split endpoint 4096 3579)/2)
    have hp : upperPayment 3578 = (81849713107:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3578+point split endpoint 4096 3579)/2 = (666150827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666150827:ℝ)/168755200)*ClassicalSixthBranch.v ((666150827:ℝ)/168755200)/ClassicalSixthBranch.r = (82824659229257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3578
  · change upperPayment 3579 ≤ upperValue ((point split endpoint 4096 3579+point split endpoint 4096 3580)/2)
    have hp : upperPayment 3579 = (81701732868:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3579+point split endpoint 4096 3580)/2 = (666175977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666175977:ℝ)/168755200)*ClassicalSixthBranch.v ((666175977:ℝ)/168755200)/ClassicalSixthBranch.r = (82805886066081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3579
  · change upperPayment 3580 ≤ upperValue ((point split endpoint 4096 3580+point split endpoint 4096 3581)/2)
    have hp : upperPayment 3580 = (81553714981:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3580+point split endpoint 4096 3581)/2 = (666201127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666201127:ℝ)/168755200)*ClassicalSixthBranch.v ((666201127:ℝ)/168755200)/ClassicalSixthBranch.r = (82787114926977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3580
  · change upperPayment 3581 ≤ upperValue ((point split endpoint 4096 3581+point split endpoint 4096 3582)/2)
    have hp : upperPayment 3581 = (81405659435:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3581+point split endpoint 4096 3582)/2 = (666226277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666226277:ℝ)/168755200)*ClassicalSixthBranch.v ((666226277:ℝ)/168755200)/ClassicalSixthBranch.r = (82768345811945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3581
  · change upperPayment 3582 ≤ upperValue ((point split endpoint 4096 3582+point split endpoint 4096 3583)/2)
    have hp : upperPayment 3582 = (81257566221:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3582+point split endpoint 4096 3583)/2 = (666251427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666251427:ℝ)/168755200)*ClassicalSixthBranch.v ((666251427:ℝ)/168755200)/ClassicalSixthBranch.r = (82749578720985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3582
  · change upperPayment 3583 ≤ upperValue ((point split endpoint 4096 3583+point split endpoint 4096 3584)/2)
    have hp : upperPayment 3583 = (81109435329:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3583+point split endpoint 4096 3584)/2 = (666276577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((666276577:ℝ)/168755200)*ClassicalSixthBranch.v ((666276577:ℝ)/168755200)/ClassicalSixthBranch.r = (82730813654097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3583
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_223
