import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints233
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_233 (j : Fin 16) : upperPayment (16*233+j.val) ≤
    upperValue ((point split endpoint 4096 (16*233+j.val)+point split endpoint 4096 (16*233+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3728 ≤ upperValue ((point split endpoint 4096 3728+point split endpoint 4096 3729)/2)
    have hp : upperPayment 3728 = (59226453329:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3728+point split endpoint 4096 3729)/2 = (669923327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669923327:ℝ)/168755200)*ClassicalSixthBranch.v ((669923327:ℝ)/168755200)/ClassicalSixthBranch.r = (80031303757457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3728
  · change upperPayment 3729 ≤ upperValue ((point split endpoint 4096 3729+point split endpoint 4096 3730)/2)
    have hp : upperPayment 3729 = (59072713700:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3729+point split endpoint 4096 3730)/2 = (669948477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669948477:ℝ)/168755200)*ClassicalSixthBranch.v ((669948477:ℝ)/168755200)/ClassicalSixthBranch.r = (80012834205081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3729
  · change upperPayment 3730 ≤ upperValue ((point split endpoint 4096 3730+point split endpoint 4096 3731)/2)
    have hp : upperPayment 3730 = (58918934902:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3730+point split endpoint 4096 3731)/2 = (669973627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669973627:ℝ)/168755200)*ClassicalSixthBranch.v ((669973627:ℝ)/168755200)/ClassicalSixthBranch.r = (79994366676777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3730
  · change upperPayment 3731 ≤ upperValue ((point split endpoint 4096 3731+point split endpoint 4096 3732)/2)
    have hp : upperPayment 3731 = (58765116923:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3731+point split endpoint 4096 3732)/2 = (669998777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669998777:ℝ)/168755200)*ClassicalSixthBranch.v ((669998777:ℝ)/168755200)/ClassicalSixthBranch.r = (79975901172545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3731
  · change upperPayment 3732 ≤ upperValue ((point split endpoint 4096 3732+point split endpoint 4096 3733)/2)
    have hp : upperPayment 3732 = (58611259755:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3732+point split endpoint 4096 3733)/2 = (670023927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670023927:ℝ)/168755200)*ClassicalSixthBranch.v ((670023927:ℝ)/168755200)/ClassicalSixthBranch.r = (79957437692385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3732
  · change upperPayment 3733 ≤ upperValue ((point split endpoint 4096 3733+point split endpoint 4096 3734)/2)
    have hp : upperPayment 3733 = (58457363385:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3733+point split endpoint 4096 3734)/2 = (670049077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670049077:ℝ)/168755200)*ClassicalSixthBranch.v ((670049077:ℝ)/168755200)/ClassicalSixthBranch.r = (79938976236297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3733
  · change upperPayment 3734 ≤ upperValue ((point split endpoint 4096 3734+point split endpoint 4096 3735)/2)
    have hp : upperPayment 3734 = (58303427804:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3734+point split endpoint 4096 3735)/2 = (670074227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670074227:ℝ)/168755200)*ClassicalSixthBranch.v ((670074227:ℝ)/168755200)/ClassicalSixthBranch.r = (79920516804281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3734
  · change upperPayment 3735 ≤ upperValue ((point split endpoint 4096 3735+point split endpoint 4096 3736)/2)
    have hp : upperPayment 3735 = (58149453001:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3735+point split endpoint 4096 3736)/2 = (670099377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670099377:ℝ)/168755200)*ClassicalSixthBranch.v ((670099377:ℝ)/168755200)/ClassicalSixthBranch.r = (775748149479:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3735
  · change upperPayment 3736 ≤ upperValue ((point split endpoint 4096 3736+point split endpoint 4096 3737)/2)
    have hp : upperPayment 3736 = (57995438966:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3736+point split endpoint 4096 3737)/2 = (670124527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670124527:ℝ)/168755200)*ClassicalSixthBranch.v ((670124527:ℝ)/168755200)/ClassicalSixthBranch.r = (79883604012465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3736
  · change upperPayment 3737 ≤ upperValue ((point split endpoint 4096 3737+point split endpoint 4096 3738)/2)
    have hp : upperPayment 3737 = (57841385689:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3737+point split endpoint 4096 3738)/2 = (670149677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670149677:ℝ)/168755200)*ClassicalSixthBranch.v ((670149677:ℝ)/168755200)/ClassicalSixthBranch.r = (79865150652665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3737
  · change upperPayment 3738 ≤ upperValue ((point split endpoint 4096 3738+point split endpoint 4096 3739)/2)
    have hp : upperPayment 3738 = (57687293157:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3738+point split endpoint 4096 3739)/2 = (670174827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670174827:ℝ)/168755200)*ClassicalSixthBranch.v ((670174827:ℝ)/168755200)/ClassicalSixthBranch.r = (79846699316937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3738
  · change upperPayment 3739 ≤ upperValue ((point split endpoint 4096 3739+point split endpoint 4096 3740)/2)
    have hp : upperPayment 3739 = (57533161363:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3739+point split endpoint 4096 3740)/2 = (670199977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670199977:ℝ)/168755200)*ClassicalSixthBranch.v ((670199977:ℝ)/168755200)/ClassicalSixthBranch.r = (79828250005281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3739
  · change upperPayment 3740 ≤ upperValue ((point split endpoint 4096 3740+point split endpoint 4096 3741)/2)
    have hp : upperPayment 3740 = (57378990294:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3740+point split endpoint 4096 3741)/2 = (670225127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670225127:ℝ)/168755200)*ClassicalSixthBranch.v ((670225127:ℝ)/168755200)/ClassicalSixthBranch.r = (79809802717697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3740
  · change upperPayment 3741 ≤ upperValue ((point split endpoint 4096 3741+point split endpoint 4096 3742)/2)
    have hp : upperPayment 3741 = (57224779940:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3741+point split endpoint 4096 3742)/2 = (670250277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670250277:ℝ)/168755200)*ClassicalSixthBranch.v ((670250277:ℝ)/168755200)/ClassicalSixthBranch.r = (79791357454185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3741
  · change upperPayment 3742 ≤ upperValue ((point split endpoint 4096 3742+point split endpoint 4096 3743)/2)
    have hp : upperPayment 3742 = (57070530291:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3742+point split endpoint 4096 3743)/2 = (670275427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670275427:ℝ)/168755200)*ClassicalSixthBranch.v ((670275427:ℝ)/168755200)/ClassicalSixthBranch.r = (79772914214745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3742
  · change upperPayment 3743 ≤ upperValue ((point split endpoint 4096 3743+point split endpoint 4096 3744)/2)
    have hp : upperPayment 3743 = (56916241336:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3743+point split endpoint 4096 3744)/2 = (670300577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670300577:ℝ)/168755200)*ClassicalSixthBranch.v ((670300577:ℝ)/168755200)/ClassicalSixthBranch.r = (79754472999377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3743
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_233
