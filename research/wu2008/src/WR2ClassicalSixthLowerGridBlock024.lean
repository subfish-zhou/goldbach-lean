import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints024
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_024 (j : Fin 16) : lowerPayment (16*24+j.val) ≤
    lowerValue ((point 2 split 4096 (16*24+j.val)+point 2 split 4096 (16*24+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 384 ≤ lowerValue ((point 2 split 4096 384+point 2 split 4096 385)/2)
    have hp : lowerPayment 384 = (57536427576:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 384+point 2 split 4096 385)/2 = (359912139:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359912139:ℝ)/168755200)/ClassicalSixthBranch.v ((359912139:ℝ)/168755200) = (784288069051:ℝ)/402119426712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_384
  · change lowerPayment 385 ≤ lowerValue ((point 2 split 4096 385+point 2 split 4096 386)/2)
    have hp : lowerPayment 385 = (57673979465:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 385+point 2 split 4096 386)/2 = (359970401:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((359970401:ℝ)/168755200)/ClassicalSixthBranch.v ((359970401:ℝ)/168755200) = (784210755377:ℝ)/402071418824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_385
  · change lowerPayment 386 ≤ lowerValue ((point 2 split 4096 386+point 2 split 4096 387)/2)
    have hp : lowerPayment 386 = (57811475666:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 386+point 2 split 4096 387)/2 = (360028663:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360028663:ℝ)/168755200)/ClassicalSixthBranch.v ((360028663:ℝ)/168755200) = (784133441703:ℝ)/402023410936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_386
  · change lowerPayment 387 ≤ lowerValue ((point 2 split 4096 387+point 2 split 4096 388)/2)
    have hp : lowerPayment 387 = (57948916228:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 387+point 2 split 4096 388)/2 = (14403477:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14403477:ℝ)/6750208)/ClassicalSixthBranch.v ((14403477:ℝ)/6750208) = (784056128029:ℝ)/401975403048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_387
  · change lowerPayment 388 ≤ lowerValue ((point 2 split 4096 388+point 2 split 4096 389)/2)
    have hp : lowerPayment 388 = (58086301200:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 388+point 2 split 4096 389)/2 = (360145187:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360145187:ℝ)/168755200)/ClassicalSixthBranch.v ((360145187:ℝ)/168755200) = (156795762871:ℝ)/80385479032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_388
  · change lowerPayment 389 ≤ lowerValue ((point 2 split 4096 389+point 2 split 4096 390)/2)
    have hp : lowerPayment 389 = (58223630631:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 389+point 2 split 4096 390)/2 = (360203449:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360203449:ℝ)/168755200)/ClassicalSixthBranch.v ((360203449:ℝ)/168755200) = (783901500681:ℝ)/401879387272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_389
  · change lowerPayment 390 ≤ lowerValue ((point 2 split 4096 390+point 2 split 4096 391)/2)
    have hp : lowerPayment 390 = (58360904571:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 390+point 2 split 4096 391)/2 = (360261711:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360261711:ℝ)/168755200)/ClassicalSixthBranch.v ((360261711:ℝ)/168755200) = (783824187007:ℝ)/401831379384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_390
  · change lowerPayment 391 ≤ lowerValue ((point 2 split 4096 391+point 2 split 4096 392)/2)
    have hp : lowerPayment 391 = (58498123070:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 391+point 2 split 4096 392)/2 = (360319973:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360319973:ℝ)/168755200)/ClassicalSixthBranch.v ((360319973:ℝ)/168755200) = (783746873333:ℝ)/401783371496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_391
  · change lowerPayment 392 ≤ lowerValue ((point 2 split 4096 392+point 2 split 4096 393)/2)
    have hp : lowerPayment 392 = (58635286176:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 392+point 2 split 4096 393)/2 = (72075647:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72075647:ℝ)/33751040)/ClassicalSixthBranch.v ((72075647:ℝ)/33751040) = (783669559659:ℝ)/401735363608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_392
  · change lowerPayment 393 ≤ lowerValue ((point 2 split 4096 393+point 2 split 4096 394)/2)
    have hp : lowerPayment 393 = (58772393939:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 393+point 2 split 4096 394)/2 = (360436497:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360436497:ℝ)/168755200)/ClassicalSixthBranch.v ((360436497:ℝ)/168755200) = (156718449197:ℝ)/80337471144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_393
  · change lowerPayment 394 ≤ lowerValue ((point 2 split 4096 394+point 2 split 4096 395)/2)
    have hp : lowerPayment 394 = (58909446408:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 394+point 2 split 4096 395)/2 = (360494759:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360494759:ℝ)/168755200)/ClassicalSixthBranch.v ((360494759:ℝ)/168755200) = (783514932311:ℝ)/401639347832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_394
  · change lowerPayment 395 ≤ lowerValue ((point 2 split 4096 395+point 2 split 4096 396)/2)
    have hp : lowerPayment 395 = (59046443633:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 395+point 2 split 4096 396)/2 = (360553021:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360553021:ℝ)/168755200)/ClassicalSixthBranch.v ((360553021:ℝ)/168755200) = (783437618637:ℝ)/401591339944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_395
  · change lowerPayment 396 ≤ lowerValue ((point 2 split 4096 396+point 2 split 4096 397)/2)
    have hp : lowerPayment 396 = (59183385662:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 396+point 2 split 4096 397)/2 = (360611283:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360611283:ℝ)/168755200)/ClassicalSixthBranch.v ((360611283:ℝ)/168755200) = (783360304963:ℝ)/401543332056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_396
  · change lowerPayment 397 ≤ lowerValue ((point 2 split 4096 397+point 2 split 4096 398)/2)
    have hp : lowerPayment 397 = (59320272545:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 397+point 2 split 4096 398)/2 = (72133909:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((72133909:ℝ)/33751040)/ClassicalSixthBranch.v ((72133909:ℝ)/33751040) = (783282991289:ℝ)/401495324168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_397
  · change lowerPayment 398 ≤ lowerValue ((point 2 split 4096 398+point 2 split 4096 399)/2)
    have hp : lowerPayment 398 = (59457104330:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 398+point 2 split 4096 399)/2 = (360727807:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360727807:ℝ)/168755200)/ClassicalSixthBranch.v ((360727807:ℝ)/168755200) = (156641135523:ℝ)/80289463256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_398
  · change lowerPayment 399 ≤ lowerValue ((point 2 split 4096 399+point 2 split 4096 400)/2)
    have hp : lowerPayment 399 = (59593881067:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 399+point 2 split 4096 400)/2 = (360786069:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((360786069:ℝ)/168755200)/ClassicalSixthBranch.v ((360786069:ℝ)/168755200) = (783128363941:ℝ)/401399308392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_399
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_024
