import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints222
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_222 (j : Fin 16) : upperPayment (16*222+j.val) ≤
    upperValue ((point split endpoint 4096 (16*222+j.val)+point split endpoint 4096 (16*222+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3552 ≤ upperValue ((point split endpoint 4096 3552+point split endpoint 4096 3553)/2)
    have hp : upperPayment 3552 = (85684016749:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3552+point split endpoint 4096 3553)/2 = (665496927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665496927:ℝ)/168755200)*ClassicalSixthBranch.v ((665496927:ℝ)/168755200)/ClassicalSixthBranch.r = (83313471921105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3552
  · change upperPayment 3553 ≤ upperValue ((point split endpoint 4096 3553+point split endpoint 4096 3554)/2)
    have hp : upperPayment 3553 = (85537011938:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3553+point split endpoint 4096 3554)/2 = (665522077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665522077:ℝ)/168755200)*ClassicalSixthBranch.v ((665522077:ℝ)/168755200)/ClassicalSixthBranch.r = (83294646132057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3553
  · change upperPayment 3554 ≤ upperValue ((point split endpoint 4096 3554+point split endpoint 4096 3555)/2)
    have hp : upperPayment 3554 = (85389969733:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3554+point split endpoint 4096 3555)/2 = (665547227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665547227:ℝ)/168755200)*ClassicalSixthBranch.v ((665547227:ℝ)/168755200)/ClassicalSixthBranch.r = (83275822367081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3554
  · change upperPayment 3555 ≤ upperValue ((point split endpoint 4096 3555+point split endpoint 4096 3556)/2)
    have hp : upperPayment 3555 = (85242890124:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3555+point split endpoint 4096 3556)/2 = (665572377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665572377:ℝ)/168755200)*ClassicalSixthBranch.v ((665572377:ℝ)/168755200)/ClassicalSixthBranch.r = (83257000626177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3555
  · change upperPayment 3556 ≤ upperValue ((point split endpoint 4096 3556+point split endpoint 4096 3557)/2)
    have hp : upperPayment 3556 = (85095773100:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3556+point split endpoint 4096 3557)/2 = (665597527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665597527:ℝ)/168755200)*ClassicalSixthBranch.v ((665597527:ℝ)/168755200)/ClassicalSixthBranch.r = (83238180909345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3556
  · change upperPayment 3557 ≤ upperValue ((point split endpoint 4096 3557+point split endpoint 4096 3558)/2)
    have hp : upperPayment 3557 = (84948618653:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3557+point split endpoint 4096 3558)/2 = (665622677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665622677:ℝ)/168755200)*ClassicalSixthBranch.v ((665622677:ℝ)/168755200)/ClassicalSixthBranch.r = (83219363216585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3557
  · change upperPayment 3558 ≤ upperValue ((point split endpoint 4096 3558+point split endpoint 4096 3559)/2)
    have hp : upperPayment 3558 = (84801426772:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3558+point split endpoint 4096 3559)/2 = (665647827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665647827:ℝ)/168755200)*ClassicalSixthBranch.v ((665647827:ℝ)/168755200)/ClassicalSixthBranch.r = (83200547547897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3558
  · change upperPayment 3559 ≤ upperValue ((point split endpoint 4096 3559+point split endpoint 4096 3560)/2)
    have hp : upperPayment 3559 = (84654197448:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3559+point split endpoint 4096 3560)/2 = (665672977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665672977:ℝ)/168755200)*ClassicalSixthBranch.v ((665672977:ℝ)/168755200)/ClassicalSixthBranch.r = (83181733903281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3559
  · change upperPayment 3560 ≤ upperValue ((point split endpoint 4096 3560+point split endpoint 4096 3561)/2)
    have hp : upperPayment 3560 = (84506930671:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3560+point split endpoint 4096 3561)/2 = (665698127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665698127:ℝ)/168755200)*ClassicalSixthBranch.v ((665698127:ℝ)/168755200)/ClassicalSixthBranch.r = (83162922282737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3560
  · change upperPayment 3561 ≤ upperValue ((point split endpoint 4096 3561+point split endpoint 4096 3562)/2)
    have hp : upperPayment 3561 = (84359626432:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3561+point split endpoint 4096 3562)/2 = (665723277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665723277:ℝ)/168755200)*ClassicalSixthBranch.v ((665723277:ℝ)/168755200)/ClassicalSixthBranch.r = (83144112686265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3561
  · change upperPayment 3562 ≤ upperValue ((point split endpoint 4096 3562+point split endpoint 4096 3563)/2)
    have hp : upperPayment 3562 = (84212284720:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3562+point split endpoint 4096 3563)/2 = (665748427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665748427:ℝ)/168755200)*ClassicalSixthBranch.v ((665748427:ℝ)/168755200)/ClassicalSixthBranch.r = (83125305113865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3562
  · change upperPayment 3563 ≤ upperValue ((point split endpoint 4096 3563+point split endpoint 4096 3564)/2)
    have hp : upperPayment 3563 = (84064905526:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3563+point split endpoint 4096 3564)/2 = (665773577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665773577:ℝ)/168755200)*ClassicalSixthBranch.v ((665773577:ℝ)/168755200)/ClassicalSixthBranch.r = (83106499565537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3563
  · change upperPayment 3564 ≤ upperValue ((point split endpoint 4096 3564+point split endpoint 4096 3565)/2)
    have hp : upperPayment 3564 = (83917488840:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3564+point split endpoint 4096 3565)/2 = (665798727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665798727:ℝ)/168755200)*ClassicalSixthBranch.v ((665798727:ℝ)/168755200)/ClassicalSixthBranch.r = (83087696041281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3564
  · change upperPayment 3565 ≤ upperValue ((point split endpoint 4096 3565+point split endpoint 4096 3566)/2)
    have hp : upperPayment 3565 = (83770034652:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3565+point split endpoint 4096 3566)/2 = (665823877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665823877:ℝ)/168755200)*ClassicalSixthBranch.v ((665823877:ℝ)/168755200)/ClassicalSixthBranch.r = (83068894541097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3565
  · change upperPayment 3566 ≤ upperValue ((point split endpoint 4096 3566+point split endpoint 4096 3567)/2)
    have hp : upperPayment 3566 = (83622542952:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3566+point split endpoint 4096 3567)/2 = (665849027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665849027:ℝ)/168755200)*ClassicalSixthBranch.v ((665849027:ℝ)/168755200)/ClassicalSixthBranch.r = (83050095064985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3566
  · change upperPayment 3567 ≤ upperValue ((point split endpoint 4096 3567+point split endpoint 4096 3568)/2)
    have hp : upperPayment 3567 = (83475013732:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3567+point split endpoint 4096 3568)/2 = (665874177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665874177:ℝ)/168755200)*ClassicalSixthBranch.v ((665874177:ℝ)/168755200)/ClassicalSixthBranch.r = (83031297612945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3567
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_222
