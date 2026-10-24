import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints228
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_228 (j : Fin 16) : upperPayment (16*228+j.val) ≤
    upperValue ((point split endpoint 4096 (16*228+j.val)+point split endpoint 4096 (16*228+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3648 ≤ upperValue ((point split endpoint 4096 3648+point split endpoint 4096 3649)/2)
    have hp : upperPayment 3648 = (71399633448:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3648+point split endpoint 4096 3649)/2 = (667911327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667911327:ℝ)/168755200)*ClassicalSixthBranch.v ((667911327:ℝ)/168755200)/ClassicalSixthBranch.r = (81515425940817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3648
  · change upperPayment 3649 ≤ upperValue ((point split endpoint 4096 3649+point split endpoint 4096 3650)/2)
    have hp : upperPayment 3649 = (71248993854:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3649+point split endpoint 4096 3650)/2 = (667936477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667936477:ℝ)/168755200)*ClassicalSixthBranch.v ((667936477:ℝ)/168755200)/ClassicalSixthBranch.r = (81496794462681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3649
  · change upperPayment 3650 ≤ upperValue ((point split endpoint 4096 3650+point split endpoint 4096 3651)/2)
    have hp : upperPayment 3650 = (71098315914:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3650+point split endpoint 4096 3651)/2 = (667961627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667961627:ℝ)/168755200)*ClassicalSixthBranch.v ((667961627:ℝ)/168755200)/ClassicalSixthBranch.r = (81478165008617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3650
  · change upperPayment 3651 ≤ upperValue ((point split endpoint 4096 3651+point split endpoint 4096 3652)/2)
    have hp : upperPayment 3651 = (70947599617:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3651+point split endpoint 4096 3652)/2 = (667986777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((667986777:ℝ)/168755200)*ClassicalSixthBranch.v ((667986777:ℝ)/168755200)/ClassicalSixthBranch.r = (81459537578625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3651
  · change upperPayment 3652 ≤ upperValue ((point split endpoint 4096 3652+point split endpoint 4096 3653)/2)
    have hp : upperPayment 3652 = (70796844954:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3652+point split endpoint 4096 3653)/2 = (668011927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668011927:ℝ)/168755200)*ClassicalSixthBranch.v ((668011927:ℝ)/168755200)/ClassicalSixthBranch.r = (81440912172705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3652
  · change upperPayment 3653 ≤ upperValue ((point split endpoint 4096 3653+point split endpoint 4096 3654)/2)
    have hp : upperPayment 3653 = (70646051914:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3653+point split endpoint 4096 3654)/2 = (668037077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668037077:ℝ)/168755200)*ClassicalSixthBranch.v ((668037077:ℝ)/168755200)/ClassicalSixthBranch.r = (81422288790857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3653
  · change upperPayment 3654 ≤ upperValue ((point split endpoint 4096 3654+point split endpoint 4096 3655)/2)
    have hp : upperPayment 3654 = (70495220486:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3654+point split endpoint 4096 3655)/2 = (668062227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668062227:ℝ)/168755200)*ClassicalSixthBranch.v ((668062227:ℝ)/168755200)/ClassicalSixthBranch.r = (81403667433081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3654
  · change upperPayment 3655 ≤ upperValue ((point split endpoint 4096 3655+point split endpoint 4096 3656)/2)
    have hp : upperPayment 3655 = (70344350662:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3655+point split endpoint 4096 3656)/2 = (668087377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668087377:ℝ)/168755200)*ClassicalSixthBranch.v ((668087377:ℝ)/168755200)/ClassicalSixthBranch.r = (81385048099377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3655
  · change upperPayment 3656 ≤ upperValue ((point split endpoint 4096 3656+point split endpoint 4096 3657)/2)
    have hp : upperPayment 3656 = (70193442431:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3656+point split endpoint 4096 3657)/2 = (668112527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668112527:ℝ)/168755200)*ClassicalSixthBranch.v ((668112527:ℝ)/168755200)/ClassicalSixthBranch.r = (81366430789745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3656
  · change upperPayment 3657 ≤ upperValue ((point split endpoint 4096 3657+point split endpoint 4096 3658)/2)
    have hp : upperPayment 3657 = (70042495783:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3657+point split endpoint 4096 3658)/2 = (668137677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668137677:ℝ)/168755200)*ClassicalSixthBranch.v ((668137677:ℝ)/168755200)/ClassicalSixthBranch.r = (81347815504185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3657
  · change upperPayment 3658 ≤ upperValue ((point split endpoint 4096 3658+point split endpoint 4096 3659)/2)
    have hp : upperPayment 3658 = (69891510707:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3658+point split endpoint 4096 3659)/2 = (668162827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668162827:ℝ)/168755200)*ClassicalSixthBranch.v ((668162827:ℝ)/168755200)/ClassicalSixthBranch.r = (81329202242697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3658
  · change upperPayment 3659 ≤ upperValue ((point split endpoint 4096 3659+point split endpoint 4096 3660)/2)
    have hp : upperPayment 3659 = (69740487193:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3659+point split endpoint 4096 3660)/2 = (668187977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668187977:ℝ)/168755200)*ClassicalSixthBranch.v ((668187977:ℝ)/168755200)/ClassicalSixthBranch.r = (81310591005281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3659
  · change upperPayment 3660 ≤ upperValue ((point split endpoint 4096 3660+point split endpoint 4096 3661)/2)
    have hp : upperPayment 3660 = (69589425232:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3660+point split endpoint 4096 3661)/2 = (668213127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668213127:ℝ)/168755200)*ClassicalSixthBranch.v ((668213127:ℝ)/168755200)/ClassicalSixthBranch.r = (81291981791937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3660
  · change upperPayment 3661 ≤ upperValue ((point split endpoint 4096 3661+point split endpoint 4096 3662)/2)
    have hp : upperPayment 3661 = (69438324813:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3661+point split endpoint 4096 3662)/2 = (668238277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668238277:ℝ)/168755200)*ClassicalSixthBranch.v ((668238277:ℝ)/168755200)/ClassicalSixthBranch.r = (81273374602665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3661
  · change upperPayment 3662 ≤ upperValue ((point split endpoint 4096 3662+point split endpoint 4096 3663)/2)
    have hp : upperPayment 3662 = (69287185926:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3662+point split endpoint 4096 3663)/2 = (668263427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668263427:ℝ)/168755200)*ClassicalSixthBranch.v ((668263427:ℝ)/168755200)/ClassicalSixthBranch.r = (81254769437465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3662
  · change upperPayment 3663 ≤ upperValue ((point split endpoint 4096 3663+point split endpoint 4096 3664)/2)
    have hp : upperPayment 3663 = (69136008560:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3663+point split endpoint 4096 3664)/2 = (668288577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668288577:ℝ)/168755200)*ClassicalSixthBranch.v ((668288577:ℝ)/168755200)/ClassicalSixthBranch.r = (81236166296337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3663
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_228
