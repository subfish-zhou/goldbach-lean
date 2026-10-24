import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints231
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_231 (j : Fin 16) : upperPayment (16*231+j.val) ≤
    upperValue ((point split endpoint 4096 (16*231+j.val)+point split endpoint 4096 (16*231+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3696 ≤ upperValue ((point split endpoint 4096 3696+point split endpoint 4096 3697)/2)
    have hp : upperPayment 3696 = (64125502399:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3696+point split endpoint 4096 3697)/2 = (669118527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669118527:ℝ)/168755200)*ClassicalSixthBranch.v ((669118527:ℝ)/168755200)/ClassicalSixthBranch.r = (80623398143505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3696
  · change upperPayment 3697 ≤ upperValue ((point split endpoint 4096 3697+point split endpoint 4096 3698)/2)
    have hp : upperPayment 3697 = (63973010692:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3697+point split endpoint 4096 3698)/2 = (669143677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669143677:ℝ)/168755200)*ClassicalSixthBranch.v ((669143677:ℝ)/168755200)/ClassicalSixthBranch.r = (80604863820825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3697
  · change upperPayment 3698 ≤ upperValue ((point split endpoint 4096 3698+point split endpoint 4096 3699)/2)
    have hp : upperPayment 3698 = (63820480149:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3698+point split endpoint 4096 3699)/2 = (669168827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669168827:ℝ)/168755200)*ClassicalSixthBranch.v ((669168827:ℝ)/168755200)/ClassicalSixthBranch.r = (80586331522217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3698
  · change upperPayment 3699 ≤ upperValue ((point split endpoint 4096 3699+point split endpoint 4096 3700)/2)
    have hp : upperPayment 3699 = (63667910758:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3699+point split endpoint 4096 3700)/2 = (669193977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669193977:ℝ)/168755200)*ClassicalSixthBranch.v ((669193977:ℝ)/168755200)/ClassicalSixthBranch.r = (80567801247681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3699
  · change upperPayment 3700 ≤ upperValue ((point split endpoint 4096 3700+point split endpoint 4096 3701)/2)
    have hp : upperPayment 3700 = (63515302509:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3700+point split endpoint 4096 3701)/2 = (669219127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669219127:ℝ)/168755200)*ClassicalSixthBranch.v ((669219127:ℝ)/168755200)/ClassicalSixthBranch.r = (80549272997217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3700
  · change upperPayment 3701 ≤ upperValue ((point split endpoint 4096 3701+point split endpoint 4096 3702)/2)
    have hp : upperPayment 3701 = (63362655393:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3701+point split endpoint 4096 3702)/2 = (669244277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669244277:ℝ)/168755200)*ClassicalSixthBranch.v ((669244277:ℝ)/168755200)/ClassicalSixthBranch.r = (80530746770825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3701
  · change upperPayment 3702 ≤ upperValue ((point split endpoint 4096 3702+point split endpoint 4096 3703)/2)
    have hp : upperPayment 3702 = (63209969399:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3702+point split endpoint 4096 3703)/2 = (669269427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669269427:ℝ)/168755200)*ClassicalSixthBranch.v ((669269427:ℝ)/168755200)/ClassicalSixthBranch.r = (80512222568505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3702
  · change upperPayment 3703 ≤ upperValue ((point split endpoint 4096 3703+point split endpoint 4096 3704)/2)
    have hp : upperPayment 3703 = (63057244516:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3703+point split endpoint 4096 3704)/2 = (669294577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669294577:ℝ)/168755200)*ClassicalSixthBranch.v ((669294577:ℝ)/168755200)/ClassicalSixthBranch.r = (80493700390257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3703
  · change upperPayment 3704 ≤ upperValue ((point split endpoint 4096 3704+point split endpoint 4096 3705)/2)
    have hp : upperPayment 3704 = (62904480734:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3704+point split endpoint 4096 3705)/2 = (669319727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669319727:ℝ)/168755200)*ClassicalSixthBranch.v ((669319727:ℝ)/168755200)/ClassicalSixthBranch.r = (80475180236081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3704
  · change upperPayment 3705 ≤ upperValue ((point split endpoint 4096 3705+point split endpoint 4096 3706)/2)
    have hp : upperPayment 3705 = (62751678043:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3705+point split endpoint 4096 3706)/2 = (669344877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669344877:ℝ)/168755200)*ClassicalSixthBranch.v ((669344877:ℝ)/168755200)/ClassicalSixthBranch.r = (80456662105977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3705
  · change upperPayment 3706 ≤ upperValue ((point split endpoint 4096 3706+point split endpoint 4096 3707)/2)
    have hp : upperPayment 3706 = (62598836432:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3706+point split endpoint 4096 3707)/2 = (669370027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669370027:ℝ)/168755200)*ClassicalSixthBranch.v ((669370027:ℝ)/168755200)/ClassicalSixthBranch.r = (80438145999945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3706
  · change upperPayment 3707 ≤ upperValue ((point split endpoint 4096 3707+point split endpoint 4096 3708)/2)
    have hp : upperPayment 3707 = (62445955892:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3707+point split endpoint 4096 3708)/2 = (669395177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669395177:ℝ)/168755200)*ClassicalSixthBranch.v ((669395177:ℝ)/168755200)/ClassicalSixthBranch.r = (80419631917985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3707
  · change upperPayment 3708 ≤ upperValue ((point split endpoint 4096 3708+point split endpoint 4096 3709)/2)
    have hp : upperPayment 3708 = (62293036411:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3708+point split endpoint 4096 3709)/2 = (669420327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669420327:ℝ)/168755200)*ClassicalSixthBranch.v ((669420327:ℝ)/168755200)/ClassicalSixthBranch.r = (80401119860097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3708
  · change upperPayment 3709 ≤ upperValue ((point split endpoint 4096 3709+point split endpoint 4096 3710)/2)
    have hp : upperPayment 3709 = (62140077979:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3709+point split endpoint 4096 3710)/2 = (669445477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669445477:ℝ)/168755200)*ClassicalSixthBranch.v ((669445477:ℝ)/168755200)/ClassicalSixthBranch.r = (80382609826281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3709
  · change upperPayment 3710 ≤ upperValue ((point split endpoint 4096 3710+point split endpoint 4096 3711)/2)
    have hp : upperPayment 3710 = (61987080587:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3710+point split endpoint 4096 3711)/2 = (669470627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669470627:ℝ)/168755200)*ClassicalSixthBranch.v ((669470627:ℝ)/168755200)/ClassicalSixthBranch.r = (80364101816537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3710
  · change upperPayment 3711 ≤ upperValue ((point split endpoint 4096 3711+point split endpoint 4096 3712)/2)
    have hp : upperPayment 3711 = (61834044222:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3711+point split endpoint 4096 3712)/2 = (6499959:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6499959:ℝ)/1638400)*ClassicalSixthBranch.v ((6499959:ℝ)/1638400)/ClassicalSixthBranch.r = (780054328455:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3711
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_231
