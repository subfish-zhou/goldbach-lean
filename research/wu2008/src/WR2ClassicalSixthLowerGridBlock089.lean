import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints089
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_089 (j : Fin 16) : lowerPayment (16*89+j.val) ≤
    lowerValue ((point 2 split 4096 (16*89+j.val)+point 2 split 4096 (16*89+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1424 ≤ lowerValue ((point 2 split 4096 1424+point 2 split 4096 1425)/2)
    have hp : lowerPayment 1424 = (177998055176:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1424+point 2 split 4096 1425)/2 = (420504619:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420504619:ℝ)/168755200)/ClassicalSixthBranch.v ((420504619:ℝ)/168755200) = (703881848091:ℝ)/352191223192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1424
  · change lowerPayment 1425 ≤ lowerValue ((point 2 split 4096 1425+point 2 split 4096 1426)/2)
    have hp : lowerPayment 1425 = (178098008340:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1425+point 2 split 4096 1426)/2 = (420562881:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420562881:ℝ)/168755200)/ClassicalSixthBranch.v ((420562881:ℝ)/168755200) = (703804534417:ℝ)/352143215304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1425
  · change lowerPayment 1426 ≤ lowerValue ((point 2 split 4096 1426+point 2 split 4096 1427)/2)
    have hp : lowerPayment 1426 = (178197940311:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1426+point 2 split 4096 1427)/2 = (420621143:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420621143:ℝ)/168755200)/ClassicalSixthBranch.v ((420621143:ℝ)/168755200) = (1399060081:ℝ)/699990472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1426
  · change lowerPayment 1427 ≤ lowerValue ((point 2 split 4096 1427+point 2 split 4096 1428)/2)
    have hp : lowerPayment 1427 = (178297851111:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1427+point 2 split 4096 1428)/2 = (84135881:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84135881:ℝ)/33751040)/ClassicalSixthBranch.v ((84135881:ℝ)/33751040) = (703649907069:ℝ)/352047199528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1427
  · change lowerPayment 1428 ≤ lowerValue ((point 2 split 4096 1428+point 2 split 4096 1429)/2)
    have hp : lowerPayment 1428 = (178397740763:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1428+point 2 split 4096 1429)/2 = (420737667:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420737667:ℝ)/168755200)/ClassicalSixthBranch.v ((420737667:ℝ)/168755200) = (140714518679:ℝ)/70399838328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1428
  · change lowerPayment 1429 ≤ lowerValue ((point 2 split 4096 1429+point 2 split 4096 1430)/2)
    have hp : lowerPayment 1429 = (178497609288:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1429+point 2 split 4096 1430)/2 = (420795929:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420795929:ℝ)/168755200)/ClassicalSixthBranch.v ((420795929:ℝ)/168755200) = (703495279721:ℝ)/351951183752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1429
  · change lowerPayment 1430 ≤ lowerValue ((point 2 split 4096 1430+point 2 split 4096 1431)/2)
    have hp : lowerPayment 1430 = (178597456710:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1430+point 2 split 4096 1431)/2 = (420854191:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420854191:ℝ)/168755200)/ClassicalSixthBranch.v ((420854191:ℝ)/168755200) = (703417966047:ℝ)/351903175864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1430
  · change lowerPayment 1431 ≤ lowerValue ((point 2 split 4096 1431+point 2 split 4096 1432)/2)
    have hp : lowerPayment 1431 = (178697283049:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1431+point 2 split 4096 1432)/2 = (420912453:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((420912453:ℝ)/168755200)/ClassicalSixthBranch.v ((420912453:ℝ)/168755200) = (703340652373:ℝ)/351855167976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1431
  · change lowerPayment 1432 ≤ lowerValue ((point 2 split 4096 1432+point 2 split 4096 1433)/2)
    have hp : lowerPayment 1432 = (178797088329:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1432+point 2 split 4096 1433)/2 = (84194143:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84194143:ℝ)/33751040)/ClassicalSixthBranch.v ((84194143:ℝ)/33751040) = (703263338699:ℝ)/351807160088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1432
  · change lowerPayment 1433 ≤ lowerValue ((point 2 split 4096 1433+point 2 split 4096 1434)/2)
    have hp : lowerPayment 1433 = (178896872571:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1433+point 2 split 4096 1434)/2 = (421028977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421028977:ℝ)/168755200)/ClassicalSixthBranch.v ((421028977:ℝ)/168755200) = (28127441001:ℝ)/14070366088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1433
  · change lowerPayment 1434 ≤ lowerValue ((point 2 split 4096 1434+point 2 split 4096 1435)/2)
    have hp : lowerPayment 1434 = (178996635798:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1434+point 2 split 4096 1435)/2 = (421087239:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421087239:ℝ)/168755200)/ClassicalSixthBranch.v ((421087239:ℝ)/168755200) = (703108711351:ℝ)/351711144312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1434
  · change lowerPayment 1435 ≤ lowerValue ((point 2 split 4096 1435+point 2 split 4096 1436)/2)
    have hp : lowerPayment 1435 = (179096378031:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1435+point 2 split 4096 1436)/2 = (421145501:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421145501:ℝ)/168755200)/ClassicalSixthBranch.v ((421145501:ℝ)/168755200) = (703031397677:ℝ)/351663136424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1435
  · change lowerPayment 1436 ≤ lowerValue ((point 2 split 4096 1436+point 2 split 4096 1437)/2)
    have hp : lowerPayment 1436 = (179196099293:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1436+point 2 split 4096 1437)/2 = (421203763:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421203763:ℝ)/168755200)/ClassicalSixthBranch.v ((421203763:ℝ)/168755200) = (702954084003:ℝ)/351615128536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1436
  · change lowerPayment 1437 ≤ lowerValue ((point 2 split 4096 1437+point 2 split 4096 1438)/2)
    have hp : lowerPayment 1437 = (179295799606:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1437+point 2 split 4096 1438)/2 = (16850481:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16850481:ℝ)/6750208)/ClassicalSixthBranch.v ((16850481:ℝ)/6750208) = (702876770329:ℝ)/351567120648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1437
  · change lowerPayment 1438 ≤ lowerValue ((point 2 split 4096 1438+point 2 split 4096 1439)/2)
    have hp : lowerPayment 1438 = (179395478993:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1438+point 2 split 4096 1439)/2 = (421320287:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421320287:ℝ)/168755200)/ClassicalSixthBranch.v ((421320287:ℝ)/168755200) = (140559891331:ℝ)/70303822552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1438
  · change lowerPayment 1439 ≤ lowerValue ((point 2 split 4096 1439+point 2 split 4096 1440)/2)
    have hp : lowerPayment 1439 = (179495137474:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1439+point 2 split 4096 1440)/2 = (421378549:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421378549:ℝ)/168755200)/ClassicalSixthBranch.v ((421378549:ℝ)/168755200) = (702722142981:ℝ)/351471104872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1439
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_089
