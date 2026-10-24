import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints153
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_153 (j : Fin 16) : lowerPayment (16*153+j.val) ≤
    lowerValue ((point 2 split 4096 (16*153+j.val)+point 2 split 4096 (16*153+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2448 ≤ lowerValue ((point 2 split 4096 2448+point 2 split 4096 2449)/2)
    have hp : lowerPayment 2448 = (272733636291:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2448+point 2 split 4096 2449)/2 = (480164907:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480164907:ℝ)/168755200)/ClassicalSixthBranch.v ((480164907:ℝ)/168755200) = (124942529183:ℝ)/60606229176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2448
  · change lowerPayment 2449 ≤ lowerValue ((point 2 split 4096 2449+point 2 split 4096 2450)/2)
    have hp : lowerPayment 2449 = (272821743400:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2449+point 2 split 4096 2450)/2 = (480223169:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480223169:ℝ)/168755200)/ClassicalSixthBranch.v ((480223169:ℝ)/168755200) = (624635332241:ℝ)/302983137992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2449
  · change lowerPayment 2450 ≤ lowerValue ((point 2 split 4096 2450+point 2 split 4096 2451)/2)
    have hp : lowerPayment 2450 = (272909847313:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2450+point 2 split 4096 2451)/2 = (480281431:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480281431:ℝ)/168755200)/ClassicalSixthBranch.v ((480281431:ℝ)/168755200) = (624558018567:ℝ)/302935130104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2450
  · change lowerPayment 2451 ≤ lowerValue ((point 2 split 4096 2451+point 2 split 4096 2452)/2)
    have hp : lowerPayment 2451 = (272997948045:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2451+point 2 split 4096 2452)/2 = (480339693:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480339693:ℝ)/168755200)/ClassicalSixthBranch.v ((480339693:ℝ)/168755200) = (624480704893:ℝ)/302887122216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2451
  · change lowerPayment 2452 ≤ lowerValue ((point 2 split 4096 2452+point 2 split 4096 2453)/2)
    have hp : lowerPayment 2452 = (273086045610:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2452+point 2 split 4096 2453)/2 = (96079591:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96079591:ℝ)/33751040)/ClassicalSixthBranch.v ((96079591:ℝ)/33751040) = (624403391219:ℝ)/302839114328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2452
  · change lowerPayment 2453 ≤ lowerValue ((point 2 split 4096 2453+point 2 split 4096 2454)/2)
    have hp : lowerPayment 2453 = (273174140023:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2453+point 2 split 4096 2454)/2 = (480456217:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480456217:ℝ)/168755200)/ClassicalSixthBranch.v ((480456217:ℝ)/168755200) = (124865215509:ℝ)/60558221288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2453
  · change lowerPayment 2454 ≤ lowerValue ((point 2 split 4096 2454+point 2 split 4096 2455)/2)
    have hp : lowerPayment 2454 = (273262231299:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2454+point 2 split 4096 2455)/2 = (480514479:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480514479:ℝ)/168755200)/ClassicalSixthBranch.v ((480514479:ℝ)/168755200) = (624248763871:ℝ)/302743098552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2454
  · change lowerPayment 2455 ≤ lowerValue ((point 2 split 4096 2455+point 2 split 4096 2456)/2)
    have hp : lowerPayment 2455 = (273350319452:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2455+point 2 split 4096 2456)/2 = (480572741:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480572741:ℝ)/168755200)/ClassicalSixthBranch.v ((480572741:ℝ)/168755200) = (624171450197:ℝ)/302695090664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2455
  · change lowerPayment 2456 ≤ lowerValue ((point 2 split 4096 2456+point 2 split 4096 2457)/2)
    have hp : lowerPayment 2456 = (273438404496:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2456+point 2 split 4096 2457)/2 = (480631003:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480631003:ℝ)/168755200)/ClassicalSixthBranch.v ((480631003:ℝ)/168755200) = (624094136523:ℝ)/302647082776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2456
  · change lowerPayment 2457 ≤ lowerValue ((point 2 split 4096 2457+point 2 split 4096 2458)/2)
    have hp : lowerPayment 2457 = (273526486447:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2457+point 2 split 4096 2458)/2 = (96137853:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96137853:ℝ)/33751040)/ClassicalSixthBranch.v ((96137853:ℝ)/33751040) = (624016822849:ℝ)/302599074888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2457
  · change lowerPayment 2458 ≤ lowerValue ((point 2 split 4096 2458+point 2 split 4096 2459)/2)
    have hp : lowerPayment 2458 = (273614565320:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2458+point 2 split 4096 2459)/2 = (480747527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480747527:ℝ)/168755200)/ClassicalSixthBranch.v ((480747527:ℝ)/168755200) = (24957580367:ℝ)/12102042680 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2458
  · change lowerPayment 2459 ≤ lowerValue ((point 2 split 4096 2459+point 2 split 4096 2460)/2)
    have hp : lowerPayment 2459 = (273702641128:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2459+point 2 split 4096 2460)/2 = (480805789:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480805789:ℝ)/168755200)/ClassicalSixthBranch.v ((480805789:ℝ)/168755200) = (623862195501:ℝ)/302503059112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2459
  · change lowerPayment 2460 ≤ lowerValue ((point 2 split 4096 2460+point 2 split 4096 2461)/2)
    have hp : lowerPayment 2460 = (273790713886:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2460+point 2 split 4096 2461)/2 = (480864051:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480864051:ℝ)/168755200)/ClassicalSixthBranch.v ((480864051:ℝ)/168755200) = (623784881827:ℝ)/302455051224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2460
  · change lowerPayment 2461 ≤ lowerValue ((point 2 split 4096 2461+point 2 split 4096 2462)/2)
    have hp : lowerPayment 2461 = (273878783610:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2461+point 2 split 4096 2462)/2 = (480922313:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480922313:ℝ)/168755200)/ClassicalSixthBranch.v ((480922313:ℝ)/168755200) = (623707568153:ℝ)/302407043336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2461
  · change lowerPayment 2462 ≤ lowerValue ((point 2 split 4096 2462+point 2 split 4096 2463)/2)
    have hp : lowerPayment 2462 = (273966850313:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2462+point 2 split 4096 2463)/2 = (19239223:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19239223:ℝ)/6750208)/ClassicalSixthBranch.v ((19239223:ℝ)/6750208) = (623630254479:ℝ)/302359035448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2462
  · change lowerPayment 2463 ≤ lowerValue ((point 2 split 4096 2463+point 2 split 4096 2464)/2)
    have hp : lowerPayment 2463 = (274054914011:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2463+point 2 split 4096 2464)/2 = (481038837:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481038837:ℝ)/168755200)/ClassicalSixthBranch.v ((481038837:ℝ)/168755200) = (124710588161:ℝ)/60462205512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2463
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_153
