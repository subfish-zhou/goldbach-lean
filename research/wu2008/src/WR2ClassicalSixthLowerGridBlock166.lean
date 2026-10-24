import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints166
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_166 (j : Fin 16) : lowerPayment (16*166+j.val) ≤
    lowerValue ((point 2 split 4096 (16*166+j.val)+point 2 split 4096 (16*166+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2656 ≤ lowerValue ((point 2 split 4096 2656+point 2 split 4096 2657)/2)
    have hp : lowerPayment 2656 = (291012603602:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2656+point 2 split 4096 2657)/2 = (492283403:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492283403:ℝ)/168755200)/ClassicalSixthBranch.v ((492283403:ℝ)/168755200) = (608631401723:ℝ)/293045505176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2656
  · change lowerPayment 2657 ≤ lowerValue ((point 2 split 4096 2657+point 2 split 4096 2658)/2)
    have hp : lowerPayment 2657 = (291100358117:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2657+point 2 split 4096 2658)/2 = (98468333:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98468333:ℝ)/33751040)/ClassicalSixthBranch.v ((98468333:ℝ)/33751040) = (608554088049:ℝ)/292997497288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2657
  · change lowerPayment 2658 ≤ lowerValue ((point 2 split 4096 2658+point 2 split 4096 2659)/2)
    have hp : lowerPayment 2658 = (291188112436:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2658+point 2 split 4096 2659)/2 = (492399927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492399927:ℝ)/168755200)/ClassicalSixthBranch.v ((492399927:ℝ)/168755200) = (24339070975:ℝ)/11717979576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2658
  · change lowerPayment 2659 ≤ lowerValue ((point 2 split 4096 2659+point 2 split 4096 2660)/2)
    have hp : lowerPayment 2659 = (291275866575:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2659+point 2 split 4096 2660)/2 = (492458189:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492458189:ℝ)/168755200)/ClassicalSixthBranch.v ((492458189:ℝ)/168755200) = (608399460701:ℝ)/292901481512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2659
  · change lowerPayment 2660 ≤ lowerValue ((point 2 split 4096 2660+point 2 split 4096 2661)/2)
    have hp : lowerPayment 2660 = (291363620548:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2660+point 2 split 4096 2661)/2 = (492516451:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492516451:ℝ)/168755200)/ClassicalSixthBranch.v ((492516451:ℝ)/168755200) = (608322147027:ℝ)/292853473624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2660
  · change lowerPayment 2661 ≤ lowerValue ((point 2 split 4096 2661+point 2 split 4096 2662)/2)
    have hp : lowerPayment 2661 = (291451374369:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2661+point 2 split 4096 2662)/2 = (492574713:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492574713:ℝ)/168755200)/ClassicalSixthBranch.v ((492574713:ℝ)/168755200) = (608244833353:ℝ)/292805465736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2661
  · change lowerPayment 2662 ≤ lowerValue ((point 2 split 4096 2662+point 2 split 4096 2663)/2)
    have hp : lowerPayment 2662 = (291539128052:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2662+point 2 split 4096 2663)/2 = (19705319:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19705319:ℝ)/6750208)/ClassicalSixthBranch.v ((19705319:ℝ)/6750208) = (608167519679:ℝ)/292757457848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2662
  · change lowerPayment 2663 ≤ lowerValue ((point 2 split 4096 2663+point 2 split 4096 2664)/2)
    have hp : lowerPayment 2663 = (291626881612:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2663+point 2 split 4096 2664)/2 = (492691237:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492691237:ℝ)/168755200)/ClassicalSixthBranch.v ((492691237:ℝ)/168755200) = (121618041201:ℝ)/58541889992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2663
  · change lowerPayment 2664 ≤ lowerValue ((point 2 split 4096 2664+point 2 split 4096 2665)/2)
    have hp : lowerPayment 2664 = (291714635062:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2664+point 2 split 4096 2665)/2 = (492749499:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492749499:ℝ)/168755200)/ClassicalSixthBranch.v ((492749499:ℝ)/168755200) = (608012892331:ℝ)/292661442072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2664
  · change lowerPayment 2665 ≤ lowerValue ((point 2 split 4096 2665+point 2 split 4096 2666)/2)
    have hp : lowerPayment 2665 = (291802388418:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2665+point 2 split 4096 2666)/2 = (492807761:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492807761:ℝ)/168755200)/ClassicalSixthBranch.v ((492807761:ℝ)/168755200) = (607935578657:ℝ)/292613434184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2665
  · change lowerPayment 2666 ≤ lowerValue ((point 2 split 4096 2666+point 2 split 4096 2667)/2)
    have hp : lowerPayment 2666 = (291890141692:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2666+point 2 split 4096 2667)/2 = (492866023:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492866023:ℝ)/168755200)/ClassicalSixthBranch.v ((492866023:ℝ)/168755200) = (607858264983:ℝ)/292565426296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2666
  · change lowerPayment 2667 ≤ lowerValue ((point 2 split 4096 2667+point 2 split 4096 2668)/2)
    have hp : lowerPayment 2667 = (291977894900:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2667+point 2 split 4096 2668)/2 = (98584857:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98584857:ℝ)/33751040)/ClassicalSixthBranch.v ((98584857:ℝ)/33751040) = (607780951309:ℝ)/292517418408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2667
  · change lowerPayment 2668 ≤ lowerValue ((point 2 split 4096 2668+point 2 split 4096 2669)/2)
    have hp : lowerPayment 2668 = (292065648056:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2668+point 2 split 4096 2669)/2 = (492982547:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492982547:ℝ)/168755200)/ClassicalSixthBranch.v ((492982547:ℝ)/168755200) = (121540727527:ℝ)/58493882104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2668
  · change lowerPayment 2669 ≤ lowerValue ((point 2 split 4096 2669+point 2 split 4096 2670)/2)
    have hp : lowerPayment 2669 = (292153401173:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2669+point 2 split 4096 2670)/2 = (493040809:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493040809:ℝ)/168755200)/ClassicalSixthBranch.v ((493040809:ℝ)/168755200) = (607626323961:ℝ)/292421402632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2669
  · change lowerPayment 2670 ≤ lowerValue ((point 2 split 4096 2670+point 2 split 4096 2671)/2)
    have hp : lowerPayment 2670 = (292241154266:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2670+point 2 split 4096 2671)/2 = (493099071:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493099071:ℝ)/168755200)/ClassicalSixthBranch.v ((493099071:ℝ)/168755200) = (607549010287:ℝ)/292373394744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2670
  · change lowerPayment 2671 ≤ lowerValue ((point 2 split 4096 2671+point 2 split 4096 2672)/2)
    have hp : lowerPayment 2671 = (292328907350:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2671+point 2 split 4096 2672)/2 = (493157333:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((493157333:ℝ)/168755200)/ClassicalSixthBranch.v ((493157333:ℝ)/168755200) = (607471696613:ℝ)/292325386856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2671
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_166
