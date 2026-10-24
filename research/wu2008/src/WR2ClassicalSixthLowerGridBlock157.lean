import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints157
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_157 (j : Fin 16) : lowerPayment (16*157+j.val) ≤
    lowerValue ((point 2 split 4096 (16*157+j.val)+point 2 split 4096 (16*157+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2512 ≤ lowerValue ((point 2 split 4096 2512+point 2 split 4096 2513)/2)
    have hp : lowerPayment 2512 = (278366657370:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2512+point 2 split 4096 2513)/2 = (19355747:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19355747:ℝ)/6750208)/ClassicalSixthBranch.v ((19355747:ℝ)/6750208) = (619764570779:ℝ)/299958641048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2512
  · change lowerPayment 2513 ≤ lowerValue ((point 2 split 4096 2513+point 2 split 4096 2514)/2)
    have hp : lowerPayment 2513 = (278454589389:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2513+point 2 split 4096 2514)/2 = (483951937:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((483951937:ℝ)/168755200)/ClassicalSixthBranch.v ((483951937:ℝ)/168755200) = (123937451421:ℝ)/59982126632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2513
  · change lowerPayment 2514 ≤ lowerValue ((point 2 split 4096 2514+point 2 split 4096 2515)/2)
    have hp : lowerPayment 2514 = (278542519145:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2514+point 2 split 4096 2515)/2 = (484010199:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484010199:ℝ)/168755200)/ClassicalSixthBranch.v ((484010199:ℝ)/168755200) = (619609943431:ℝ)/299862625272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2514
  · change lowerPayment 2515 ≤ lowerValue ((point 2 split 4096 2515+point 2 split 4096 2516)/2)
    have hp : lowerPayment 2515 = (278630446652:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2515+point 2 split 4096 2516)/2 = (484068461:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484068461:ℝ)/168755200)/ClassicalSixthBranch.v ((484068461:ℝ)/168755200) = (619532629757:ℝ)/299814617384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2515
  · change lowerPayment 2516 ≤ lowerValue ((point 2 split 4096 2516+point 2 split 4096 2517)/2)
    have hp : lowerPayment 2516 = (278718371926:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2516+point 2 split 4096 2517)/2 = (484126723:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484126723:ℝ)/168755200)/ClassicalSixthBranch.v ((484126723:ℝ)/168755200) = (619455316083:ℝ)/299766609496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2516
  · change lowerPayment 2517 ≤ lowerValue ((point 2 split 4096 2517+point 2 split 4096 2518)/2)
    have hp : lowerPayment 2517 = (278806294981:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2517+point 2 split 4096 2518)/2 = (96836997:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96836997:ℝ)/33751040)/ClassicalSixthBranch.v ((96836997:ℝ)/33751040) = (619378002409:ℝ)/299718601608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2517
  · change lowerPayment 2518 ≤ lowerValue ((point 2 split 4096 2518+point 2 split 4096 2519)/2)
    have hp : lowerPayment 2518 = (278894215832:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2518+point 2 split 4096 2519)/2 = (484243247:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484243247:ℝ)/168755200)/ClassicalSixthBranch.v ((484243247:ℝ)/168755200) = (123860137747:ℝ)/59934118744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2518
  · change lowerPayment 2519 ≤ lowerValue ((point 2 split 4096 2519+point 2 split 4096 2520)/2)
    have hp : lowerPayment 2519 = (278982134492:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2519+point 2 split 4096 2520)/2 = (484301509:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484301509:ℝ)/168755200)/ClassicalSixthBranch.v ((484301509:ℝ)/168755200) = (619223375061:ℝ)/299622585832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2519
  · change lowerPayment 2520 ≤ lowerValue ((point 2 split 4096 2520+point 2 split 4096 2521)/2)
    have hp : lowerPayment 2520 = (279070050976:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2520+point 2 split 4096 2521)/2 = (484359771:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484359771:ℝ)/168755200)/ClassicalSixthBranch.v ((484359771:ℝ)/168755200) = (619146061387:ℝ)/299574577944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2520
  · change lowerPayment 2521 ≤ lowerValue ((point 2 split 4096 2521+point 2 split 4096 2522)/2)
    have hp : lowerPayment 2521 = (279157965300:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2521+point 2 split 4096 2522)/2 = (484418033:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484418033:ℝ)/168755200)/ClassicalSixthBranch.v ((484418033:ℝ)/168755200) = (619068747713:ℝ)/299526570056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2521
  · change lowerPayment 2522 ≤ lowerValue ((point 2 split 4096 2522+point 2 split 4096 2523)/2)
    have hp : lowerPayment 2522 = (279245877476:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2522+point 2 split 4096 2523)/2 = (96895259:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96895259:ℝ)/33751040)/ClassicalSixthBranch.v ((96895259:ℝ)/33751040) = (618991434039:ℝ)/299478562168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2522
  · change lowerPayment 2523 ≤ lowerValue ((point 2 split 4096 2523+point 2 split 4096 2524)/2)
    have hp : lowerPayment 2523 = (279333787521:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2523+point 2 split 4096 2524)/2 = (4704219:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4704219:ℝ)/1638400)/ClassicalSixthBranch.v ((4704219:ℝ)/1638400) = (1201774991:ℝ)/581418552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2523
  · change lowerPayment 2524 ≤ lowerValue ((point 2 split 4096 2524+point 2 split 4096 2525)/2)
    have hp : lowerPayment 2524 = (279421695448:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2524+point 2 split 4096 2525)/2 = (484592819:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484592819:ℝ)/168755200)/ClassicalSixthBranch.v ((484592819:ℝ)/168755200) = (618836806691:ℝ)/299382546392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2524
  · change lowerPayment 2525 ≤ lowerValue ((point 2 split 4096 2525+point 2 split 4096 2526)/2)
    have hp : lowerPayment 2525 = (279509601271:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2525+point 2 split 4096 2526)/2 = (484651081:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484651081:ℝ)/168755200)/ClassicalSixthBranch.v ((484651081:ℝ)/168755200) = (618759493017:ℝ)/299334538504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2525
  · change lowerPayment 2526 ≤ lowerValue ((point 2 split 4096 2526+point 2 split 4096 2527)/2)
    have hp : lowerPayment 2526 = (279597505006:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2526+point 2 split 4096 2527)/2 = (484709343:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((484709343:ℝ)/168755200)/ClassicalSixthBranch.v ((484709343:ℝ)/168755200) = (618682179343:ℝ)/299286530616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2526
  · change lowerPayment 2527 ≤ lowerValue ((point 2 split 4096 2527+point 2 split 4096 2528)/2)
    have hp : lowerPayment 2527 = (279685406667:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2527+point 2 split 4096 2528)/2 = (96953521:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96953521:ℝ)/33751040)/ClassicalSixthBranch.v ((96953521:ℝ)/33751040) = (618604865669:ℝ)/299238522728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2527
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_157
