import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints034
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_034 (j : Fin 16) : lowerPayment (16*34+j.val) ≤
    lowerValue ((point 2 split 4096 (16*34+j.val)+point 2 split 4096 (16*34+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 544 ≤ lowerValue ((point 2 split 4096 544+point 2 split 4096 545)/2)
    have hp : lowerPayment 544 = (78868392637:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 544+point 2 split 4096 545)/2 = (369234059:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369234059:ℝ)/168755200)/ClassicalSixthBranch.v ((369234059:ℝ)/168755200) = (771917881211:ℝ)/394438164632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_544
  · change lowerPayment 545 ≤ lowerValue ((point 2 split 4096 545+point 2 split 4096 546)/2)
    have hp : lowerPayment 545 = (78997635100:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 545+point 2 split 4096 546)/2 = (369292321:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369292321:ℝ)/168755200)/ClassicalSixthBranch.v ((369292321:ℝ)/168755200) = (771840567537:ℝ)/394390156744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_545
  · change lowerPayment 546 ≤ lowerValue ((point 2 split 4096 546+point 2 split 4096 547)/2)
    have hp : lowerPayment 546 = (79126829252:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 546+point 2 split 4096 547)/2 = (369350583:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369350583:ℝ)/168755200)/ClassicalSixthBranch.v ((369350583:ℝ)/168755200) = (771763253863:ℝ)/394342148856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_546
  · change lowerPayment 547 ≤ lowerValue ((point 2 split 4096 547+point 2 split 4096 548)/2)
    have hp : lowerPayment 547 = (79255975136:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 547+point 2 split 4096 548)/2 = (73881769:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73881769:ℝ)/33751040)/ClassicalSixthBranch.v ((73881769:ℝ)/33751040) = (771685940189:ℝ)/394294140968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_547
  · change lowerPayment 548 ≤ lowerValue ((point 2 split 4096 548+point 2 split 4096 549)/2)
    have hp : lowerPayment 548 = (79385072794:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 548+point 2 split 4096 549)/2 = (369467107:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369467107:ℝ)/168755200)/ClassicalSixthBranch.v ((369467107:ℝ)/168755200) = (154321725303:ℝ)/78849226616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_548
  · change lowerPayment 549 ≤ lowerValue ((point 2 split 4096 549+point 2 split 4096 550)/2)
    have hp : lowerPayment 549 = (79514122269:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 549+point 2 split 4096 550)/2 = (369525369:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369525369:ℝ)/168755200)/ClassicalSixthBranch.v ((369525369:ℝ)/168755200) = (771531312841:ℝ)/394198125192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_549
  · change lowerPayment 550 ≤ lowerValue ((point 2 split 4096 550+point 2 split 4096 551)/2)
    have hp : lowerPayment 550 = (79643123604:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 550+point 2 split 4096 551)/2 = (369583631:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369583631:ℝ)/168755200)/ClassicalSixthBranch.v ((369583631:ℝ)/168755200) = (771453999167:ℝ)/394150117304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_550
  · change lowerPayment 551 ≤ lowerValue ((point 2 split 4096 551+point 2 split 4096 552)/2)
    have hp : lowerPayment 551 = (79772076841:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 551+point 2 split 4096 552)/2 = (369641893:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369641893:ℝ)/168755200)/ClassicalSixthBranch.v ((369641893:ℝ)/168755200) = (771376685493:ℝ)/394102109416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_551
  · change lowerPayment 552 ≤ lowerValue ((point 2 split 4096 552+point 2 split 4096 553)/2)
    have hp : lowerPayment 552 = (79900982024:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 552+point 2 split 4096 553)/2 = (73940031:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73940031:ℝ)/33751040)/ClassicalSixthBranch.v ((73940031:ℝ)/33751040) = (771299371819:ℝ)/394054101528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_552
  · change lowerPayment 553 ≤ lowerValue ((point 2 split 4096 553+point 2 split 4096 554)/2)
    have hp : lowerPayment 553 = (80029839195:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 553+point 2 split 4096 554)/2 = (369758417:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369758417:ℝ)/168755200)/ClassicalSixthBranch.v ((369758417:ℝ)/168755200) = (154244411629:ℝ)/78801218728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_553
  · change lowerPayment 554 ≤ lowerValue ((point 2 split 4096 554+point 2 split 4096 555)/2)
    have hp : lowerPayment 554 = (80158648396:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 554+point 2 split 4096 555)/2 = (369816679:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369816679:ℝ)/168755200)/ClassicalSixthBranch.v ((369816679:ℝ)/168755200) = (771144744471:ℝ)/393958085752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_554
  · change lowerPayment 555 ≤ lowerValue ((point 2 split 4096 555+point 2 split 4096 556)/2)
    have hp : lowerPayment 555 = (80287409671:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 555+point 2 split 4096 556)/2 = (369874941:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369874941:ℝ)/168755200)/ClassicalSixthBranch.v ((369874941:ℝ)/168755200) = (771067430797:ℝ)/393910077864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_555
  · change lowerPayment 556 ≤ lowerValue ((point 2 split 4096 556+point 2 split 4096 557)/2)
    have hp : lowerPayment 556 = (80416123060:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 556+point 2 split 4096 557)/2 = (369933203:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((369933203:ℝ)/168755200)/ClassicalSixthBranch.v ((369933203:ℝ)/168755200) = (770990117123:ℝ)/393862069976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_556
  · change lowerPayment 557 ≤ lowerValue ((point 2 split 4096 557+point 2 split 4096 558)/2)
    have hp : lowerPayment 557 = (80544788608:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 557+point 2 split 4096 558)/2 = (73998293:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73998293:ℝ)/33751040)/ClassicalSixthBranch.v ((73998293:ℝ)/33751040) = (770912803449:ℝ)/393814062088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_557
  · change lowerPayment 558 ≤ lowerValue ((point 2 split 4096 558+point 2 split 4096 559)/2)
    have hp : lowerPayment 558 = (80673406357:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 558+point 2 split 4096 559)/2 = (370049727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370049727:ℝ)/168755200)/ClassicalSixthBranch.v ((370049727:ℝ)/168755200) = (30833419591:ℝ)/15750642168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_558
  · change lowerPayment 559 ≤ lowerValue ((point 2 split 4096 559+point 2 split 4096 560)/2)
    have hp : lowerPayment 559 = (80801976348:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 559+point 2 split 4096 560)/2 = (370107989:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((370107989:ℝ)/168755200)/ClassicalSixthBranch.v ((370107989:ℝ)/168755200) = (770758176101:ℝ)/393718046312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_559
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_034
