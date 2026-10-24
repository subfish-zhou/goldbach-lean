import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints086
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_086 (j : Fin 16) : lowerPayment (16*86+j.val) ≤
    lowerValue ((point 2 split 4096 (16*86+j.val)+point 2 split 4096 (16*86+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1376 ≤ lowerValue ((point 2 split 4096 1376+point 2 split 4096 1377)/2)
    have hp : lowerPayment 1376 = (173174940904:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1376+point 2 split 4096 1377)/2 = (417708043:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417708043:ℝ)/168755200)/ClassicalSixthBranch.v ((417708043:ℝ)/168755200) = (707592904443:ℝ)/354495601816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1376
  · change lowerPayment 1377 ≤ lowerValue ((point 2 split 4096 1377+point 2 split 4096 1378)/2)
    have hp : lowerPayment 1377 = (173275937761:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1377+point 2 split 4096 1378)/2 = (83553261:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83553261:ℝ)/33751040)/ClassicalSixthBranch.v ((83553261:ℝ)/33751040) = (707515590769:ℝ)/354447593928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1377
  · change lowerPayment 1378 ≤ lowerValue ((point 2 split 4096 1378+point 2 split 4096 1379)/2)
    have hp : lowerPayment 1378 = (173376912341:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1378+point 2 split 4096 1379)/2 = (417824567:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417824567:ℝ)/168755200)/ClassicalSixthBranch.v ((417824567:ℝ)/168755200) = (141487655419:ℝ)/70879917208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1378
  · change lowerPayment 1379 ≤ lowerValue ((point 2 split 4096 1379+point 2 split 4096 1380)/2)
    have hp : lowerPayment 1379 = (173477864666:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1379+point 2 split 4096 1380)/2 = (417882829:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417882829:ℝ)/168755200)/ClassicalSixthBranch.v ((417882829:ℝ)/168755200) = (707360963421:ℝ)/354351578152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1379
  · change lowerPayment 1380 ≤ lowerValue ((point 2 split 4096 1380+point 2 split 4096 1381)/2)
    have hp : lowerPayment 1380 = (173578794761:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1380+point 2 split 4096 1381)/2 = (417941091:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417941091:ℝ)/168755200)/ClassicalSixthBranch.v ((417941091:ℝ)/168755200) = (707283649747:ℝ)/354303570264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1380
  · change lowerPayment 1381 ≤ lowerValue ((point 2 split 4096 1381+point 2 split 4096 1382)/2)
    have hp : lowerPayment 1381 = (173679702648:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1381+point 2 split 4096 1382)/2 = (417999353:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((417999353:ℝ)/168755200)/ClassicalSixthBranch.v ((417999353:ℝ)/168755200) = (707206336073:ℝ)/354255562376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1381
  · change lowerPayment 1382 ≤ lowerValue ((point 2 split 4096 1382+point 2 split 4096 1383)/2)
    have hp : lowerPayment 1382 = (173780588349:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1382+point 2 split 4096 1383)/2 = (83611523:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((83611523:ℝ)/33751040)/ClassicalSixthBranch.v ((83611523:ℝ)/33751040) = (707129022399:ℝ)/354207554488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1382
  · change lowerPayment 1383 ≤ lowerValue ((point 2 split 4096 1383+point 2 split 4096 1384)/2)
    have hp : lowerPayment 1383 = (173881451888:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1383+point 2 split 4096 1384)/2 = (418115877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((418115877:ℝ)/168755200)/ClassicalSixthBranch.v ((418115877:ℝ)/168755200) = (28282068349:ℝ)/14166381864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1383
  · change lowerPayment 1384 ≤ lowerValue ((point 2 split 4096 1384+point 2 split 4096 1385)/2)
    have hp : lowerPayment 1384 = (173982293287:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1384+point 2 split 4096 1385)/2 = (418174139:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((418174139:ℝ)/168755200)/ClassicalSixthBranch.v ((418174139:ℝ)/168755200) = (706974395051:ℝ)/354111538712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1384
  · change lowerPayment 1385 ≤ lowerValue ((point 2 split 4096 1385+point 2 split 4096 1386)/2)
    have hp : lowerPayment 1385 = (174083112569:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1385+point 2 split 4096 1386)/2 = (418232401:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((418232401:ℝ)/168755200)/ClassicalSixthBranch.v ((418232401:ℝ)/168755200) = (706897081377:ℝ)/354063530824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1385
  · change lowerPayment 1386 ≤ lowerValue ((point 2 split 4096 1386+point 2 split 4096 1387)/2)
    have hp : lowerPayment 1386 = (174183909757:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1386+point 2 split 4096 1387)/2 = (418290663:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((418290663:ℝ)/168755200)/ClassicalSixthBranch.v ((418290663:ℝ)/168755200) = (706819767703:ℝ)/354015522936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1386
  · change lowerPayment 1387 ≤ lowerValue ((point 2 split 4096 1387+point 2 split 4096 1388)/2)
    have hp : lowerPayment 1387 = (174284684874:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1387+point 2 split 4096 1388)/2 = (16733957:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16733957:ℝ)/6750208)/ClassicalSixthBranch.v ((16733957:ℝ)/6750208) = (706742454029:ℝ)/353967515048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1387
  · change lowerPayment 1388 ≤ lowerValue ((point 2 split 4096 1388+point 2 split 4096 1389)/2)
    have hp : lowerPayment 1388 = (174385437942:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1388+point 2 split 4096 1389)/2 = (418407187:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((418407187:ℝ)/168755200)/ClassicalSixthBranch.v ((418407187:ℝ)/168755200) = (141333028071:ℝ)/70783901432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1388
  · change lowerPayment 1389 ≤ lowerValue ((point 2 split 4096 1389+point 2 split 4096 1390)/2)
    have hp : lowerPayment 1389 = (174486168985:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1389+point 2 split 4096 1390)/2 = (418465449:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((418465449:ℝ)/168755200)/ClassicalSixthBranch.v ((418465449:ℝ)/168755200) = (706587826681:ℝ)/353871499272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1389
  · change lowerPayment 1390 ≤ lowerValue ((point 2 split 4096 1390+point 2 split 4096 1391)/2)
    have hp : lowerPayment 1390 = (174586878025:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1390+point 2 split 4096 1391)/2 = (4063337:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4063337:ℝ)/1638400)/ClassicalSixthBranch.v ((4063337:ℝ)/1638400) = (6859325369:ℝ)/3435179528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1390
  · change lowerPayment 1391 ≤ lowerValue ((point 2 split 4096 1391+point 2 split 4096 1392)/2)
    have hp : lowerPayment 1391 = (174687565085:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1391+point 2 split 4096 1392)/2 = (418581973:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((418581973:ℝ)/168755200)/ClassicalSixthBranch.v ((418581973:ℝ)/168755200) = (706433199333:ℝ)/353775483496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1391
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_086
