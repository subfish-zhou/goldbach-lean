import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints036
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_036 (j : Fin 16) : lowerPayment (16*36+j.val) ≤
    lowerValue ((point 2 split 4096 (16*36+j.val)+point 2 split 4096 (16*36+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 576 ≤ lowerValue ((point 2 split 4096 576+point 2 split 4096 577)/2)
    have hp : lowerPayment 576 = (82980400270:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 576+point 2 split 4096 577)/2 = (371098443:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371098443:ℝ)/168755200)/ClassicalSixthBranch.v ((371098443:ℝ)/168755200) = (769443843643:ℝ)/392901912216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_576
  · change lowerPayment 577 ≤ lowerValue ((point 2 split 4096 577+point 2 split 4096 578)/2)
    have hp : lowerPayment 577 = (83108117842:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 577+point 2 split 4096 578)/2 = (74231341:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74231341:ℝ)/33751040)/ClassicalSixthBranch.v ((74231341:ℝ)/33751040) = (769366529969:ℝ)/392853904328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_577
  · change lowerPayment 578 ≤ lowerValue ((point 2 split 4096 578+point 2 split 4096 579)/2)
    have hp : lowerPayment 578 = (83235788456:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 578+point 2 split 4096 579)/2 = (371214967:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371214967:ℝ)/168755200)/ClassicalSixthBranch.v ((371214967:ℝ)/168755200) = (153857843259:ℝ)/78561179288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_578
  · change lowerPayment 579 ≤ lowerValue ((point 2 split 4096 579+point 2 split 4096 580)/2)
    have hp : lowerPayment 579 = (83363412153:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 579+point 2 split 4096 580)/2 = (371273229:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371273229:ℝ)/168755200)/ClassicalSixthBranch.v ((371273229:ℝ)/168755200) = (769211902621:ℝ)/392757888552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_579
  · change lowerPayment 580 ≤ lowerValue ((point 2 split 4096 580+point 2 split 4096 581)/2)
    have hp : lowerPayment 580 = (83490988974:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 580+point 2 split 4096 581)/2 = (371331491:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371331491:ℝ)/168755200)/ClassicalSixthBranch.v ((371331491:ℝ)/168755200) = (769134588947:ℝ)/392709880664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_580
  · change lowerPayment 581 ≤ lowerValue ((point 2 split 4096 581+point 2 split 4096 582)/2)
    have hp : lowerPayment 581 = (83618518962:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 581+point 2 split 4096 582)/2 = (371389753:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371389753:ℝ)/168755200)/ClassicalSixthBranch.v ((371389753:ℝ)/168755200) = (769057275273:ℝ)/392661872776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_581
  · change lowerPayment 582 ≤ lowerValue ((point 2 split 4096 582+point 2 split 4096 583)/2)
    have hp : lowerPayment 582 = (83746002158:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 582+point 2 split 4096 583)/2 = (74289603:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74289603:ℝ)/33751040)/ClassicalSixthBranch.v ((74289603:ℝ)/33751040) = (768979961599:ℝ)/392613864888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_582
  · change lowerPayment 583 ≤ lowerValue ((point 2 split 4096 583+point 2 split 4096 584)/2)
    have hp : lowerPayment 583 = (83873438603:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 583+point 2 split 4096 584)/2 = (371506277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371506277:ℝ)/168755200)/ClassicalSixthBranch.v ((371506277:ℝ)/168755200) = (30756105917:ℝ)/15702634280 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_583
  · change lowerPayment 584 ≤ lowerValue ((point 2 split 4096 584+point 2 split 4096 585)/2)
    have hp : lowerPayment 584 = (84000828340:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 584+point 2 split 4096 585)/2 = (371564539:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371564539:ℝ)/168755200)/ClassicalSixthBranch.v ((371564539:ℝ)/168755200) = (768825334251:ℝ)/392517849112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_584
  · change lowerPayment 585 ≤ lowerValue ((point 2 split 4096 585+point 2 split 4096 586)/2)
    have hp : lowerPayment 585 = (84128171409:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 585+point 2 split 4096 586)/2 = (371622801:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371622801:ℝ)/168755200)/ClassicalSixthBranch.v ((371622801:ℝ)/168755200) = (768748020577:ℝ)/392469841224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_585
  · change lowerPayment 586 ≤ lowerValue ((point 2 split 4096 586+point 2 split 4096 587)/2)
    have hp : lowerPayment 586 = (84255467851:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 586+point 2 split 4096 587)/2 = (371681063:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371681063:ℝ)/168755200)/ClassicalSixthBranch.v ((371681063:ℝ)/168755200) = (768670706903:ℝ)/392421833336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_586
  · change lowerPayment 587 ≤ lowerValue ((point 2 split 4096 587+point 2 split 4096 588)/2)
    have hp : lowerPayment 587 = (84382717709:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 587+point 2 split 4096 588)/2 = (14869573:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14869573:ℝ)/6750208)/ClassicalSixthBranch.v ((14869573:ℝ)/6750208) = (768593393229:ℝ)/392373825448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_587
  · change lowerPayment 588 ≤ lowerValue ((point 2 split 4096 588+point 2 split 4096 589)/2)
    have hp : lowerPayment 588 = (84509921024:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 588+point 2 split 4096 589)/2 = (371797587:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371797587:ℝ)/168755200)/ClassicalSixthBranch.v ((371797587:ℝ)/168755200) = (153703215911:ℝ)/78465163512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_588
  · change lowerPayment 589 ≤ lowerValue ((point 2 split 4096 589+point 2 split 4096 590)/2)
    have hp : lowerPayment 589 = (84637077836:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 589+point 2 split 4096 590)/2 = (371855849:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371855849:ℝ)/168755200)/ClassicalSixthBranch.v ((371855849:ℝ)/168755200) = (768438765881:ℝ)/392277809672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_589
  · change lowerPayment 590 ≤ lowerValue ((point 2 split 4096 590+point 2 split 4096 591)/2)
    have hp : lowerPayment 590 = (84764188188:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 590+point 2 split 4096 591)/2 = (371914111:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371914111:ℝ)/168755200)/ClassicalSixthBranch.v ((371914111:ℝ)/168755200) = (768361452207:ℝ)/392229801784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_590
  · change lowerPayment 591 ≤ lowerValue ((point 2 split 4096 591+point 2 split 4096 592)/2)
    have hp : lowerPayment 591 = (84891252120:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 591+point 2 split 4096 592)/2 = (371972373:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((371972373:ℝ)/168755200)/ClassicalSixthBranch.v ((371972373:ℝ)/168755200) = (768284138533:ℝ)/392181793896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_591
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_036
