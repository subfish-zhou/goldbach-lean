import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints031
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_031 (j : Fin 16) : lowerPayment (16*31+j.val) ≤
    lowerValue ((point 2 split 4096 (16*31+j.val)+point 2 split 4096 (16*31+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 496 ≤ lowerValue ((point 2 split 4096 496+point 2 split 4096 497)/2)
    have hp : lowerPayment 496 = (72607090837:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 496+point 2 split 4096 497)/2 = (366437483:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366437483:ℝ)/168755200)/ClassicalSixthBranch.v ((366437483:ℝ)/168755200) = (775628937563:ℝ)/396742543256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_496
  · change lowerPayment 497 ≤ lowerValue ((point 2 split 4096 497+point 2 split 4096 498)/2)
    have hp : lowerPayment 497 = (72738703390:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 497+point 2 split 4096 498)/2 = (73299149:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73299149:ℝ)/33751040)/ClassicalSixthBranch.v ((73299149:ℝ)/33751040) = (775551623889:ℝ)/396694535368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_497
  · change lowerPayment 498 ≤ lowerValue ((point 2 split 4096 498+point 2 split 4096 499)/2)
    have hp : lowerPayment 498 = (72870265530:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 498+point 2 split 4096 499)/2 = (366554007:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366554007:ℝ)/168755200)/ClassicalSixthBranch.v ((366554007:ℝ)/168755200) = (155094862043:ℝ)/79329305496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_498
  · change lowerPayment 499 ≤ lowerValue ((point 2 split 4096 499+point 2 split 4096 500)/2)
    have hp : lowerPayment 499 = (73001777300:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 499+point 2 split 4096 500)/2 = (366612269:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366612269:ℝ)/168755200)/ClassicalSixthBranch.v ((366612269:ℝ)/168755200) = (775396996541:ℝ)/396598519592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_499
  · change lowerPayment 500 ≤ lowerValue ((point 2 split 4096 500+point 2 split 4096 501)/2)
    have hp : lowerPayment 500 = (73133238747:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 500+point 2 split 4096 501)/2 = (366670531:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366670531:ℝ)/168755200)/ClassicalSixthBranch.v ((366670531:ℝ)/168755200) = (775319682867:ℝ)/396550511704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_500
  · change lowerPayment 501 ≤ lowerValue ((point 2 split 4096 501+point 2 split 4096 502)/2)
    have hp : lowerPayment 501 = (73264649913:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 501+point 2 split 4096 502)/2 = (366728793:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366728793:ℝ)/168755200)/ClassicalSixthBranch.v ((366728793:ℝ)/168755200) = (775242369193:ℝ)/396502503816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_501
  · change lowerPayment 502 ≤ lowerValue ((point 2 split 4096 502+point 2 split 4096 503)/2)
    have hp : lowerPayment 502 = (73396010845:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 502+point 2 split 4096 503)/2 = (73357411:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73357411:ℝ)/33751040)/ClassicalSixthBranch.v ((73357411:ℝ)/33751040) = (775165055519:ℝ)/396454495928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_502
  · change lowerPayment 503 ≤ lowerValue ((point 2 split 4096 503+point 2 split 4096 504)/2)
    have hp : lowerPayment 503 = (73527321587:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 503+point 2 split 4096 504)/2 = (366845317:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366845317:ℝ)/168755200)/ClassicalSixthBranch.v ((366845317:ℝ)/168755200) = (155017548369:ℝ)/79281297608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_503
  · change lowerPayment 504 ≤ lowerValue ((point 2 split 4096 504+point 2 split 4096 505)/2)
    have hp : lowerPayment 504 = (73658582182:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 504+point 2 split 4096 505)/2 = (366903579:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366903579:ℝ)/168755200)/ClassicalSixthBranch.v ((366903579:ℝ)/168755200) = (775010428171:ℝ)/396358480152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_504
  · change lowerPayment 505 ≤ lowerValue ((point 2 split 4096 505+point 2 split 4096 506)/2)
    have hp : lowerPayment 505 = (73789792676:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 505+point 2 split 4096 506)/2 = (366961841:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((366961841:ℝ)/168755200)/ClassicalSixthBranch.v ((366961841:ℝ)/168755200) = (774933114497:ℝ)/396310472264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_505
  · change lowerPayment 506 ≤ lowerValue ((point 2 split 4096 506+point 2 split 4096 507)/2)
    have hp : lowerPayment 506 = (73920953114:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 506+point 2 split 4096 507)/2 = (367020103:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367020103:ℝ)/168755200)/ClassicalSixthBranch.v ((367020103:ℝ)/168755200) = (774855800823:ℝ)/396262464376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_506
  · change lowerPayment 507 ≤ lowerValue ((point 2 split 4096 507+point 2 split 4096 508)/2)
    have hp : lowerPayment 507 = (74052063538:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 507+point 2 split 4096 508)/2 = (73415673:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73415673:ℝ)/33751040)/ClassicalSixthBranch.v ((73415673:ℝ)/33751040) = (774778487149:ℝ)/396214456488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_507
  · change lowerPayment 508 ≤ lowerValue ((point 2 split 4096 508+point 2 split 4096 509)/2)
    have hp : lowerPayment 508 = (74183123995:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 508+point 2 split 4096 509)/2 = (367136627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367136627:ℝ)/168755200)/ClassicalSixthBranch.v ((367136627:ℝ)/168755200) = (30988046939:ℝ)/15846657944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_508
  · change lowerPayment 509 ≤ lowerValue ((point 2 split 4096 509+point 2 split 4096 510)/2)
    have hp : lowerPayment 509 = (74314134527:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 509+point 2 split 4096 510)/2 = (367194889:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367194889:ℝ)/168755200)/ClassicalSixthBranch.v ((367194889:ℝ)/168755200) = (774623859801:ℝ)/396118440712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_509
  · change lowerPayment 510 ≤ lowerValue ((point 2 split 4096 510+point 2 split 4096 511)/2)
    have hp : lowerPayment 510 = (74445095180:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 510+point 2 split 4096 511)/2 = (367253151:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367253151:ℝ)/168755200)/ClassicalSixthBranch.v ((367253151:ℝ)/168755200) = (774546546127:ℝ)/396070432824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_510
  · change lowerPayment 511 ≤ lowerValue ((point 2 split 4096 511+point 2 split 4096 512)/2)
    have hp : lowerPayment 511 = (74576005998:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 511+point 2 split 4096 512)/2 = (367311413:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367311413:ℝ)/168755200)/ClassicalSixthBranch.v ((367311413:ℝ)/168755200) = (774469232453:ℝ)/396022424936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_511
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_031
