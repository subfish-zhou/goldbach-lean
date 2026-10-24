import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints222
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_222 (j : Fin 16) : lowerPayment (16*222+j.val) ≤
    lowerValue ((point 2 split 4096 (16*222+j.val)+point 2 split 4096 (16*222+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3552 ≤ lowerValue ((point 2 split 4096 3552+point 2 split 4096 3553)/2)
    have hp : lowerPayment 3552 = (371260081317:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3552+point 2 split 4096 3553)/2 = (108897231:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108897231:ℝ)/33751040)/ClassicalSixthBranch.v ((108897231:ℝ)/33751040) = (539358349819:ℝ)/250030437528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3552
  · change lowerPayment 3553 ≤ lowerValue ((point 2 split 4096 3553+point 2 split 4096 3554)/2)
    have hp : lowerPayment 3553 = (371353389473:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3553+point 2 split 4096 3554)/2 = (5286839:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((5286839:ℝ)/1638400)/ClassicalSixthBranch.v ((5286839:ℝ)/1638400) = (1047147643:ℝ)/485402776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3553
  · change lowerPayment 3554 ≤ lowerValue ((point 2 split 4096 3554+point 2 split 4096 3555)/2)
    have hp : lowerPayment 3554 = (371446710460:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3554+point 2 split 4096 3555)/2 = (544602679:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544602679:ℝ)/168755200)/ClassicalSixthBranch.v ((544602679:ℝ)/168755200) = (539203722471:ℝ)/249934421752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3554
  · change lowerPayment 3555 ≤ lowerValue ((point 2 split 4096 3555+point 2 split 4096 3556)/2)
    have hp : lowerPayment 3555 = (371540044293:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3555+point 2 split 4096 3556)/2 = (544660941:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544660941:ℝ)/168755200)/ClassicalSixthBranch.v ((544660941:ℝ)/168755200) = (539126408797:ℝ)/249886413864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3555
  · change lowerPayment 3556 ≤ lowerValue ((point 2 split 4096 3556+point 2 split 4096 3557)/2)
    have hp : lowerPayment 3556 = (371633390988:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3556+point 2 split 4096 3557)/2 = (544719203:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544719203:ℝ)/168755200)/ClassicalSixthBranch.v ((544719203:ℝ)/168755200) = (539049095123:ℝ)/249838405976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3556
  · change lowerPayment 3557 ≤ lowerValue ((point 2 split 4096 3557+point 2 split 4096 3558)/2)
    have hp : lowerPayment 3557 = (371726750562:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3557+point 2 split 4096 3558)/2 = (108955493:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((108955493:ℝ)/33751040)/ClassicalSixthBranch.v ((108955493:ℝ)/33751040) = (538971781449:ℝ)/249790398088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3557
  · change lowerPayment 3558 ≤ lowerValue ((point 2 split 4096 3558+point 2 split 4096 3559)/2)
    have hp : lowerPayment 3558 = (371820123030:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3558+point 2 split 4096 3559)/2 = (544835727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544835727:ℝ)/168755200)/ClassicalSixthBranch.v ((544835727:ℝ)/168755200) = (21555778711:ℝ)/9989695608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3558
  · change lowerPayment 3559 ≤ lowerValue ((point 2 split 4096 3559+point 2 split 4096 3560)/2)
    have hp : lowerPayment 3559 = (371913508407:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3559+point 2 split 4096 3560)/2 = (544893989:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544893989:ℝ)/168755200)/ClassicalSixthBranch.v ((544893989:ℝ)/168755200) = (538817154101:ℝ)/249694382312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3559
  · change lowerPayment 3560 ≤ lowerValue ((point 2 split 4096 3560+point 2 split 4096 3561)/2)
    have hp : lowerPayment 3560 = (372006906710:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3560+point 2 split 4096 3561)/2 = (544952251:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((544952251:ℝ)/168755200)/ClassicalSixthBranch.v ((544952251:ℝ)/168755200) = (538739840427:ℝ)/249646374424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3560
  · change lowerPayment 3561 ≤ lowerValue ((point 2 split 4096 3561+point 2 split 4096 3562)/2)
    have hp : lowerPayment 3561 = (372100317954:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3561+point 2 split 4096 3562)/2 = (545010513:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545010513:ℝ)/168755200)/ClassicalSixthBranch.v ((545010513:ℝ)/168755200) = (538662526753:ℝ)/249598366536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3561
  · change lowerPayment 3562 ≤ lowerValue ((point 2 split 4096 3562+point 2 split 4096 3563)/2)
    have hp : lowerPayment 3562 = (372193742155:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3562+point 2 split 4096 3563)/2 = (21802751:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21802751:ℝ)/6750208)/ClassicalSixthBranch.v ((21802751:ℝ)/6750208) = (538585213079:ℝ)/249550358648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3562
  · change lowerPayment 3563 ≤ lowerValue ((point 2 split 4096 3563+point 2 split 4096 3564)/2)
    have hp : lowerPayment 3563 = (372287179329:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3563+point 2 split 4096 3564)/2 = (545127037:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545127037:ℝ)/168755200)/ClassicalSixthBranch.v ((545127037:ℝ)/168755200) = (107701579881:ℝ)/49900470152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3563
  · change lowerPayment 3564 ≤ lowerValue ((point 2 split 4096 3564+point 2 split 4096 3565)/2)
    have hp : lowerPayment 3564 = (372380629492:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3564+point 2 split 4096 3565)/2 = (545185299:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545185299:ℝ)/168755200)/ClassicalSixthBranch.v ((545185299:ℝ)/168755200) = (538430585731:ℝ)/249454342872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3564
  · change lowerPayment 3565 ≤ lowerValue ((point 2 split 4096 3565+point 2 split 4096 3566)/2)
    have hp : lowerPayment 3565 = (372474092659:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3565+point 2 split 4096 3566)/2 = (545243561:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545243561:ℝ)/168755200)/ClassicalSixthBranch.v ((545243561:ℝ)/168755200) = (538353272057:ℝ)/249406334984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3565
  · change lowerPayment 3566 ≤ lowerValue ((point 2 split 4096 3566+point 2 split 4096 3567)/2)
    have hp : lowerPayment 3566 = (372567568847:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3566+point 2 split 4096 3567)/2 = (545301823:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((545301823:ℝ)/168755200)/ClassicalSixthBranch.v ((545301823:ℝ)/168755200) = (538275958383:ℝ)/249358327096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3566
  · change lowerPayment 3567 ≤ lowerValue ((point 2 split 4096 3567+point 2 split 4096 3568)/2)
    have hp : lowerPayment 3567 = (372661058070:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3567+point 2 split 4096 3568)/2 = (109072017:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109072017:ℝ)/33751040)/ClassicalSixthBranch.v ((109072017:ℝ)/33751040) = (538198644709:ℝ)/249310319208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3567
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_222
