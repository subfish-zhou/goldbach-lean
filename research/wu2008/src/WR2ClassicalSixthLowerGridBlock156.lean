import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints156
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_156 (j : Fin 16) : lowerPayment (16*156+j.val) ≤
    lowerValue ((point 2 split 4096 (16*156+j.val)+point 2 split 4096 (16*156+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2496 ≤ lowerValue ((point 2 split 4096 2496+point 2 split 4096 2497)/2)
    have hp : lowerPayment 2496 = (276959425508:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2496+point 2 split 4096 2497)/2 = (482961483:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482961483:ℝ)/168755200)/ClassicalSixthBranch.v ((482961483:ℝ)/168755200) = (621001589563:ℝ)/300726767256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2496
  · change lowerPayment 2497 ≤ lowerValue ((point 2 split 4096 2497+point 2 split 4096 2498)/2)
    have hp : lowerPayment 2497 = (277047395704:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2497+point 2 split 4096 2498)/2 = (96603949:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96603949:ℝ)/33751040)/ClassicalSixthBranch.v ((96603949:ℝ)/33751040) = (620924275889:ℝ)/300678759368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2497
  · change lowerPayment 2498 ≤ lowerValue ((point 2 split 4096 2498+point 2 split 4096 2499)/2)
    have hp : lowerPayment 2498 = (277135363404:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2498+point 2 split 4096 2499)/2 = (483078007:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483078007:ℝ)/168755200)/ClassicalSixthBranch.v ((483078007:ℝ)/168755200) = (124169392443:ℝ)/60126150296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2498
  · change lowerPayment 2499 ≤ lowerValue ((point 2 split 4096 2499+point 2 split 4096 2500)/2)
    have hp : lowerPayment 2499 = (277223328624:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2499+point 2 split 4096 2500)/2 = (483136269:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483136269:ℝ)/168755200)/ClassicalSixthBranch.v ((483136269:ℝ)/168755200) = (620769648541:ℝ)/300582743592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2499
  · change lowerPayment 2500 ≤ lowerValue ((point 2 split 4096 2500+point 2 split 4096 2501)/2)
    have hp : lowerPayment 2500 = (277311291378:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2500+point 2 split 4096 2501)/2 = (483194531:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483194531:ℝ)/168755200)/ClassicalSixthBranch.v ((483194531:ℝ)/168755200) = (620692334867:ℝ)/300534735704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2500
  · change lowerPayment 2501 ≤ lowerValue ((point 2 split 4096 2501+point 2 split 4096 2502)/2)
    have hp : lowerPayment 2501 = (277399251681:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2501+point 2 split 4096 2502)/2 = (483252793:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483252793:ℝ)/168755200)/ClassicalSixthBranch.v ((483252793:ℝ)/168755200) = (620615021193:ℝ)/300486727816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2501
  · change lowerPayment 2502 ≤ lowerValue ((point 2 split 4096 2502+point 2 split 4096 2503)/2)
    have hp : lowerPayment 2502 = (277487209546:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2502+point 2 split 4096 2503)/2 = (96662211:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96662211:ℝ)/33751040)/ClassicalSixthBranch.v ((96662211:ℝ)/33751040) = (620537707519:ℝ)/300438719928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2502
  · change lowerPayment 2503 ≤ lowerValue ((point 2 split 4096 2503+point 2 split 4096 2504)/2)
    have hp : lowerPayment 2503 = (277575164989:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2503+point 2 split 4096 2504)/2 = (483369317:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483369317:ℝ)/168755200)/ClassicalSixthBranch.v ((483369317:ℝ)/168755200) = (124092078769:ℝ)/60078142408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2503
  · change lowerPayment 2504 ≤ lowerValue ((point 2 split 4096 2504+point 2 split 4096 2505)/2)
    have hp : lowerPayment 2504 = (277663118025:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2504+point 2 split 4096 2505)/2 = (483427579:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483427579:ℝ)/168755200)/ClassicalSixthBranch.v ((483427579:ℝ)/168755200) = (620383080171:ℝ)/300342704152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2504
  · change lowerPayment 2505 ≤ lowerValue ((point 2 split 4096 2505+point 2 split 4096 2506)/2)
    have hp : lowerPayment 2505 = (277751068667:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2505+point 2 split 4096 2506)/2 = (483485841:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483485841:ℝ)/168755200)/ClassicalSixthBranch.v ((483485841:ℝ)/168755200) = (620305766497:ℝ)/300294696264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2505
  · change lowerPayment 2506 ≤ lowerValue ((point 2 split 4096 2506+point 2 split 4096 2507)/2)
    have hp : lowerPayment 2506 = (277839016931:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2506+point 2 split 4096 2507)/2 = (483544103:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483544103:ℝ)/168755200)/ClassicalSixthBranch.v ((483544103:ℝ)/168755200) = (620228452823:ℝ)/300246688376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2506
  · change lowerPayment 2507 ≤ lowerValue ((point 2 split 4096 2507+point 2 split 4096 2508)/2)
    have hp : lowerPayment 2507 = (277926962830:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2507+point 2 split 4096 2508)/2 = (96720473:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96720473:ℝ)/33751040)/ClassicalSixthBranch.v ((96720473:ℝ)/33751040) = (620151139149:ℝ)/300198680488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2507
  · change lowerPayment 2508 ≤ lowerValue ((point 2 split 4096 2508+point 2 split 4096 2509)/2)
    have hp : lowerPayment 2508 = (278014906379:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2508+point 2 split 4096 2509)/2 = (483660627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483660627:ℝ)/168755200)/ClassicalSixthBranch.v ((483660627:ℝ)/168755200) = (24802953019:ℝ)/12006026904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2508
  · change lowerPayment 2509 ≤ lowerValue ((point 2 split 4096 2509+point 2 split 4096 2510)/2)
    have hp : lowerPayment 2509 = (278102847593:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2509+point 2 split 4096 2510)/2 = (483718889:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483718889:ℝ)/168755200)/ClassicalSixthBranch.v ((483718889:ℝ)/168755200) = (619996511801:ℝ)/300102664712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2509
  · change lowerPayment 2510 ≤ lowerValue ((point 2 split 4096 2510+point 2 split 4096 2511)/2)
    have hp : lowerPayment 2510 = (278190786487:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2510+point 2 split 4096 2511)/2 = (483777151:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483777151:ℝ)/168755200)/ClassicalSixthBranch.v ((483777151:ℝ)/168755200) = (619919198127:ℝ)/300054656824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2510
  · change lowerPayment 2511 ≤ lowerValue ((point 2 split 4096 2511+point 2 split 4096 2512)/2)
    have hp : lowerPayment 2511 = (278278723074:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2511+point 2 split 4096 2512)/2 = (483835413:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483835413:ℝ)/168755200)/ClassicalSixthBranch.v ((483835413:ℝ)/168755200) = (619841884453:ℝ)/300006648936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2511
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_156
