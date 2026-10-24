import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints161
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_161 (j : Fin 16) : lowerPayment (16*161+j.val) ≤
    lowerValue ((point 2 split 4096 (16*161+j.val)+point 2 split 4096 (16*161+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2576 ≤ lowerValue ((point 2 split 4096 2576+point 2 split 4096 2577)/2)
    have hp : lowerPayment 2576 = (283990347933:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2576+point 2 split 4096 2577)/2 = (487622443:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487622443:ℝ)/168755200)/ClassicalSixthBranch.v ((487622443:ℝ)/168755200) = (614816495643:ℝ)/296886136216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2576
  · change lowerPayment 2577 ≤ lowerValue ((point 2 split 4096 2577+point 2 split 4096 2578)/2)
    have hp : lowerPayment 2577 = (284078164290:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2577+point 2 split 4096 2578)/2 = (97536141:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97536141:ℝ)/33751040)/ClassicalSixthBranch.v ((97536141:ℝ)/33751040) = (614739181969:ℝ)/296838128328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2577
  · change lowerPayment 2578 ≤ lowerValue ((point 2 split 4096 2578+point 2 split 4096 2579)/2)
    have hp : lowerPayment 2578 = (284165979308:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2578+point 2 split 4096 2579)/2 = (487738967:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487738967:ℝ)/168755200)/ClassicalSixthBranch.v ((487738967:ℝ)/168755200) = (122932373659:ℝ)/59358024088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2578
  · change lowerPayment 2579 ≤ lowerValue ((point 2 split 4096 2579+point 2 split 4096 2580)/2)
    have hp : lowerPayment 2579 = (284253793001:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2579+point 2 split 4096 2580)/2 = (487797229:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487797229:ℝ)/168755200)/ClassicalSixthBranch.v ((487797229:ℝ)/168755200) = (614584554621:ℝ)/296742112552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2579
  · change lowerPayment 2580 ≤ lowerValue ((point 2 split 4096 2580+point 2 split 4096 2581)/2)
    have hp : lowerPayment 2580 = (284341605385:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2580+point 2 split 4096 2581)/2 = (487855491:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487855491:ℝ)/168755200)/ClassicalSixthBranch.v ((487855491:ℝ)/168755200) = (614507240947:ℝ)/296694104664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2580
  · change lowerPayment 2581 ≤ lowerValue ((point 2 split 4096 2581+point 2 split 4096 2582)/2)
    have hp : lowerPayment 2581 = (284429416472:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2581+point 2 split 4096 2582)/2 = (487913753:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((487913753:ℝ)/168755200)/ClassicalSixthBranch.v ((487913753:ℝ)/168755200) = (614429927273:ℝ)/296646096776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2581
  · change lowerPayment 2582 ≤ lowerValue ((point 2 split 4096 2582+point 2 split 4096 2583)/2)
    have hp : lowerPayment 2582 = (284517226279:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2582+point 2 split 4096 2583)/2 = (97594403:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97594403:ℝ)/33751040)/ClassicalSixthBranch.v ((97594403:ℝ)/33751040) = (614352613599:ℝ)/296598088888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2582
  · change lowerPayment 2583 ≤ lowerValue ((point 2 split 4096 2583+point 2 split 4096 2584)/2)
    have hp : lowerPayment 2583 = (284605034818:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2583+point 2 split 4096 2584)/2 = (488030277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488030277:ℝ)/168755200)/ClassicalSixthBranch.v ((488030277:ℝ)/168755200) = (24571011997:ℝ)/11862003240 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2583
  · change lowerPayment 2584 ≤ lowerValue ((point 2 split 4096 2584+point 2 split 4096 2585)/2)
    have hp : lowerPayment 2584 = (284692842105:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2584+point 2 split 4096 2585)/2 = (488088539:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488088539:ℝ)/168755200)/ClassicalSixthBranch.v ((488088539:ℝ)/168755200) = (614197986251:ℝ)/296502073112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2584
  · change lowerPayment 2585 ≤ lowerValue ((point 2 split 4096 2585+point 2 split 4096 2586)/2)
    have hp : lowerPayment 2585 = (284780648154:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2585+point 2 split 4096 2586)/2 = (488146801:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488146801:ℝ)/168755200)/ClassicalSixthBranch.v ((488146801:ℝ)/168755200) = (614120672577:ℝ)/296454065224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2585
  · change lowerPayment 2586 ≤ lowerValue ((point 2 split 4096 2586+point 2 split 4096 2587)/2)
    have hp : lowerPayment 2586 = (284868452979:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2586+point 2 split 4096 2587)/2 = (488205063:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488205063:ℝ)/168755200)/ClassicalSixthBranch.v ((488205063:ℝ)/168755200) = (614043358903:ℝ)/296406057336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2586
  · change lowerPayment 2587 ≤ lowerValue ((point 2 split 4096 2587+point 2 split 4096 2588)/2)
    have hp : lowerPayment 2587 = (284956256594:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2587+point 2 split 4096 2588)/2 = (19530533:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19530533:ℝ)/6750208)/ClassicalSixthBranch.v ((19530533:ℝ)/6750208) = (613966045229:ℝ)/296358049448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2587
  · change lowerPayment 2588 ≤ lowerValue ((point 2 split 4096 2588+point 2 split 4096 2589)/2)
    have hp : lowerPayment 2588 = (285044059014:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2588+point 2 split 4096 2589)/2 = (488321587:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488321587:ℝ)/168755200)/ClassicalSixthBranch.v ((488321587:ℝ)/168755200) = (122777746311:ℝ)/59262008312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2588
  · change lowerPayment 2589 ≤ lowerValue ((point 2 split 4096 2589+point 2 split 4096 2590)/2)
    have hp : lowerPayment 2589 = (285131860253:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2589+point 2 split 4096 2590)/2 = (488379849:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488379849:ℝ)/168755200)/ClassicalSixthBranch.v ((488379849:ℝ)/168755200) = (613811417881:ℝ)/296262033672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2589
  · change lowerPayment 2590 ≤ lowerValue ((point 2 split 4096 2590+point 2 split 4096 2591)/2)
    have hp : lowerPayment 2590 = (285219660326:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2590+point 2 split 4096 2591)/2 = (488438111:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488438111:ℝ)/168755200)/ClassicalSixthBranch.v ((488438111:ℝ)/168755200) = (613734104207:ℝ)/296214025784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2590
  · change lowerPayment 2591 ≤ lowerValue ((point 2 split 4096 2591+point 2 split 4096 2592)/2)
    have hp : lowerPayment 2591 = (285307459246:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2591+point 2 split 4096 2592)/2 = (488496373:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488496373:ℝ)/168755200)/ClassicalSixthBranch.v ((488496373:ℝ)/168755200) = (613656790533:ℝ)/296166017896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2591
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_161
