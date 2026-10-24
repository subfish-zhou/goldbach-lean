import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints224
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_224 (j : Fin 16) : lowerPayment (16*224+j.val) ≤
    lowerValue ((point 2 split 4096 (16*224+j.val)+point 2 split 4096 (16*224+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3584 ≤ lowerValue ((point 2 split 4096 3584+point 2 split 4096 3585)/2)
    have hp : lowerPayment 3584 = (374252384772:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3584+point 2 split 4096 3585)/2 = (546350539:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546350539:ℝ)/168755200)/ClassicalSixthBranch.v ((546350539:ℝ)/168755200) = (536884312251:ℝ)/248494185112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3584
  · change lowerPayment 3585 ≤ lowerValue ((point 2 split 4096 3585+point 2 split 4096 3586)/2)
    have hp : lowerPayment 3585 = (374346111360:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3585+point 2 split 4096 3586)/2 = (546408801:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546408801:ℝ)/168755200)/ClassicalSixthBranch.v ((546408801:ℝ)/168755200) = (536806998577:ℝ)/248446177224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3585
  · change lowerPayment 3586 ≤ lowerValue ((point 2 split 4096 3586+point 2 split 4096 3587)/2)
    have hp : lowerPayment 3586 = (374439851285:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3586+point 2 split 4096 3587)/2 = (546467063:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546467063:ℝ)/168755200)/ClassicalSixthBranch.v ((546467063:ℝ)/168755200) = (536729684903:ℝ)/248398169336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3586
  · change lowerPayment 3587 ≤ lowerValue ((point 2 split 4096 3587+point 2 split 4096 3588)/2)
    have hp : lowerPayment 3587 = (374533604564:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3587+point 2 split 4096 3588)/2 = (21861013:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((21861013:ℝ)/6750208)/ClassicalSixthBranch.v ((21861013:ℝ)/6750208) = (536652371229:ℝ)/248350161448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3587
  · change lowerPayment 3588 ≤ lowerValue ((point 2 split 4096 3588+point 2 split 4096 3589)/2)
    have hp : lowerPayment 3588 = (374627371213:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3588+point 2 split 4096 3589)/2 = (546583587:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546583587:ℝ)/168755200)/ClassicalSixthBranch.v ((546583587:ℝ)/168755200) = (107315011511:ℝ)/49660430712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3588
  · change lowerPayment 3589 ≤ lowerValue ((point 2 split 4096 3589+point 2 split 4096 3590)/2)
    have hp : lowerPayment 3589 = (374721151248:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3589+point 2 split 4096 3590)/2 = (546641849:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546641849:ℝ)/168755200)/ClassicalSixthBranch.v ((546641849:ℝ)/168755200) = (536497743881:ℝ)/248254145672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3589
  · change lowerPayment 3590 ≤ lowerValue ((point 2 split 4096 3590+point 2 split 4096 3591)/2)
    have hp : lowerPayment 3590 = (374814944684:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3590+point 2 split 4096 3591)/2 = (546700111:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546700111:ℝ)/168755200)/ClassicalSixthBranch.v ((546700111:ℝ)/168755200) = (536420430207:ℝ)/248206137784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3590
  · change lowerPayment 3591 ≤ lowerValue ((point 2 split 4096 3591+point 2 split 4096 3592)/2)
    have hp : lowerPayment 3591 = (374908751538:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3591+point 2 split 4096 3592)/2 = (546758373:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546758373:ℝ)/168755200)/ClassicalSixthBranch.v ((546758373:ℝ)/168755200) = (536343116533:ℝ)/248158129896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3591
  · change lowerPayment 3592 ≤ lowerValue ((point 2 split 4096 3592+point 2 split 4096 3593)/2)
    have hp : lowerPayment 3592 = (375002571826:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3592+point 2 split 4096 3593)/2 = (109363327:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109363327:ℝ)/33751040)/ClassicalSixthBranch.v ((109363327:ℝ)/33751040) = (536265802859:ℝ)/248110122008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3592
  · change lowerPayment 3593 ≤ lowerValue ((point 2 split 4096 3593+point 2 split 4096 3594)/2)
    have hp : lowerPayment 3593 = (375096405563:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3593+point 2 split 4096 3594)/2 = (546874897:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546874897:ℝ)/168755200)/ClassicalSixthBranch.v ((546874897:ℝ)/168755200) = (107237697837:ℝ)/49612422824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3593
  · change lowerPayment 3594 ≤ lowerValue ((point 2 split 4096 3594+point 2 split 4096 3595)/2)
    have hp : lowerPayment 3594 = (375190252765:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3594+point 2 split 4096 3595)/2 = (546933159:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546933159:ℝ)/168755200)/ClassicalSixthBranch.v ((546933159:ℝ)/168755200) = (536111175511:ℝ)/248014106232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3594
  · change lowerPayment 3595 ≤ lowerValue ((point 2 split 4096 3595+point 2 split 4096 3596)/2)
    have hp : lowerPayment 3595 = (375284113449:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3595+point 2 split 4096 3596)/2 = (546991421:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((546991421:ℝ)/168755200)/ClassicalSixthBranch.v ((546991421:ℝ)/168755200) = (536033861837:ℝ)/247966098344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3595
  · change lowerPayment 3596 ≤ lowerValue ((point 2 split 4096 3596+point 2 split 4096 3597)/2)
    have hp : lowerPayment 3596 = (375377987631:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3596+point 2 split 4096 3597)/2 = (547049683:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547049683:ℝ)/168755200)/ClassicalSixthBranch.v ((547049683:ℝ)/168755200) = (535956548163:ℝ)/247918090456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3596
  · change lowerPayment 3597 ≤ lowerValue ((point 2 split 4096 3597+point 2 split 4096 3598)/2)
    have hp : lowerPayment 3597 = (375471875326:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3597+point 2 split 4096 3598)/2 = (109421589:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((109421589:ℝ)/33751040)/ClassicalSixthBranch.v ((109421589:ℝ)/33751040) = (535879234489:ℝ)/247870082568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3597
  · change lowerPayment 3598 ≤ lowerValue ((point 2 split 4096 3598+point 2 split 4096 3599)/2)
    have hp : lowerPayment 3598 = (375565776550:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3598+point 2 split 4096 3599)/2 = (547166207:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547166207:ℝ)/168755200)/ClassicalSixthBranch.v ((547166207:ℝ)/168755200) = (107160384163:ℝ)/49564414936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3598
  · change lowerPayment 3599 ≤ lowerValue ((point 2 split 4096 3599+point 2 split 4096 3600)/2)
    have hp : lowerPayment 3599 = (375659691320:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3599+point 2 split 4096 3600)/2 = (547224469:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((547224469:ℝ)/168755200)/ClassicalSixthBranch.v ((547224469:ℝ)/168755200) = (535724607141:ℝ)/247774066792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3599
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_224
