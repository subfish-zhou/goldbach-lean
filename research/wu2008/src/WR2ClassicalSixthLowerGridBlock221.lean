import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints221
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_221 (j : Fin 16) : lowerPayment (16*221+j.val) ≤
    lowerValue ((point 2 split 4096 (16*221+j.val)+point 2 split 4096 (16*221+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3536 ≤ lowerValue ((point 2 split 4096 3536+point 2 split 4096 3537)/2)
    have hp : lowerPayment 3536 = (369768882963:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3536+point 2 split 4096 3537)/2 = (543553963:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543553963:ℝ)/168755200)/ClassicalSixthBranch.v ((543553963:ℝ)/168755200) = (540595368603:ℝ)/250798563736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3536
  · change lowerPayment 3537 ≤ lowerValue ((point 2 split 4096 3537+point 2 split 4096 3538)/2)
    have hp : lowerPayment 3537 = (369861987967:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3537+point 2 split 4096 3538)/2 = (21744489:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21744489:ℝ)/6750208)/ClassicalSixthBranch.v ((21744489:ℝ)/6750208) = (540518054929:ℝ)/250750555848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3537
  · change lowerPayment 3538 ≤ lowerValue ((point 2 split 4096 3538+point 2 split 4096 3539)/2)
    have hp : lowerPayment 3538 = (369955105550:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3538+point 2 split 4096 3539)/2 = (543670487:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543670487:ℝ)/168755200)/ClassicalSixthBranch.v ((543670487:ℝ)/168755200) = (108088148251:ℝ)/50140509592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3538
  · change lowerPayment 3539 ≤ lowerValue ((point 2 split 4096 3539+point 2 split 4096 3540)/2)
    have hp : lowerPayment 3539 = (370048235727:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3539+point 2 split 4096 3540)/2 = (543728749:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543728749:ℝ)/168755200)/ClassicalSixthBranch.v ((543728749:ℝ)/168755200) = (540363427581:ℝ)/250654540072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3539
  · change lowerPayment 3540 ≤ lowerValue ((point 2 split 4096 3540+point 2 split 4096 3541)/2)
    have hp : lowerPayment 3540 = (370141378515:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3540+point 2 split 4096 3541)/2 = (543787011:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543787011:ℝ)/168755200)/ClassicalSixthBranch.v ((543787011:ℝ)/168755200) = (540286113907:ℝ)/250606532184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3540
  · change lowerPayment 3541 ≤ lowerValue ((point 2 split 4096 3541+point 2 split 4096 3542)/2)
    have hp : lowerPayment 3541 = (370234533930:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3541+point 2 split 4096 3542)/2 = (543845273:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543845273:ℝ)/168755200)/ClassicalSixthBranch.v ((543845273:ℝ)/168755200) = (540208800233:ℝ)/250558524296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3541
  · change lowerPayment 3542 ≤ lowerValue ((point 2 split 4096 3542+point 2 split 4096 3543)/2)
    have hp : lowerPayment 3542 = (370327701986:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3542+point 2 split 4096 3543)/2 = (108780707:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108780707:ℝ)/33751040)/ClassicalSixthBranch.v ((108780707:ℝ)/33751040) = (540131486559:ℝ)/250510516408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3542
  · change lowerPayment 3543 ≤ lowerValue ((point 2 split 4096 3543+point 2 split 4096 3544)/2)
    have hp : lowerPayment 3543 = (370420882700:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3543+point 2 split 4096 3544)/2 = (543961797:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((543961797:ℝ)/168755200)/ClassicalSixthBranch.v ((543961797:ℝ)/168755200) = (108010834577:ℝ)/50092501704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3543
  · change lowerPayment 3544 ≤ lowerValue ((point 2 split 4096 3544+point 2 split 4096 3545)/2)
    have hp : lowerPayment 3544 = (370514076088:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3544+point 2 split 4096 3545)/2 = (544020059:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544020059:ℝ)/168755200)/ClassicalSixthBranch.v ((544020059:ℝ)/168755200) = (539976859211:ℝ)/250414500632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3544
  · change lowerPayment 3545 ≤ lowerValue ((point 2 split 4096 3545+point 2 split 4096 3546)/2)
    have hp : lowerPayment 3545 = (370607282165:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3545+point 2 split 4096 3546)/2 = (544078321:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544078321:ℝ)/168755200)/ClassicalSixthBranch.v ((544078321:ℝ)/168755200) = (539899545537:ℝ)/250366492744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3545
  · change lowerPayment 3546 ≤ lowerValue ((point 2 split 4096 3546+point 2 split 4096 3547)/2)
    have hp : lowerPayment 3546 = (370700500946:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3546+point 2 split 4096 3547)/2 = (544136583:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544136583:ℝ)/168755200)/ClassicalSixthBranch.v ((544136583:ℝ)/168755200) = (539822231863:ℝ)/250318484856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3546
  · change lowerPayment 3547 ≤ lowerValue ((point 2 split 4096 3547+point 2 split 4096 3548)/2)
    have hp : lowerPayment 3547 = (370793732448:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3547+point 2 split 4096 3548)/2 = (108838969:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108838969:ℝ)/33751040)/ClassicalSixthBranch.v ((108838969:ℝ)/33751040) = (539744918189:ℝ)/250270476968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3547
  · change lowerPayment 3548 ≤ lowerValue ((point 2 split 4096 3548+point 2 split 4096 3549)/2)
    have hp : lowerPayment 3548 = (370886976686:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3548+point 2 split 4096 3549)/2 = (544253107:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544253107:ℝ)/168755200)/ClassicalSixthBranch.v ((544253107:ℝ)/168755200) = (107933520903:ℝ)/50044493816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3548
  · change lowerPayment 3549 ≤ lowerValue ((point 2 split 4096 3549+point 2 split 4096 3550)/2)
    have hp : lowerPayment 3549 = (370980233677:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3549+point 2 split 4096 3550)/2 = (544311369:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544311369:ℝ)/168755200)/ClassicalSixthBranch.v ((544311369:ℝ)/168755200) = (539590290841:ℝ)/250174461192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3549
  · change lowerPayment 3550 ≤ lowerValue ((point 2 split 4096 3550+point 2 split 4096 3551)/2)
    have hp : lowerPayment 3550 = (371073503435:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3550+point 2 split 4096 3551)/2 = (544369631:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544369631:ℝ)/168755200)/ClassicalSixthBranch.v ((544369631:ℝ)/168755200) = (539512977167:ℝ)/250126453304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3550
  · change lowerPayment 3551 ≤ lowerValue ((point 2 split 4096 3551+point 2 split 4096 3552)/2)
    have hp : lowerPayment 3551 = (371166785976:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3551+point 2 split 4096 3552)/2 = (544427893:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544427893:ℝ)/168755200)/ClassicalSixthBranch.v ((544427893:ℝ)/168755200) = (539435663493:ℝ)/250078445416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3551
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_221
