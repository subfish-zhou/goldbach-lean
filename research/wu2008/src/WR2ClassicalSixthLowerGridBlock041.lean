import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints041
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_041 (j : Fin 16) : lowerPayment (16*41+j.val) ≤
    lowerValue ((point 2 split 4096 (16*41+j.val)+point 2 split 4096 (16*41+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 656 ≤ lowerValue ((point 2 split 4096 656+point 2 split 4096 657)/2)
    have hp : lowerPayment 656 = (93052784253:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 656+point 2 split 4096 657)/2 = (375759403:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375759403:ℝ)/168755200)/ClassicalSixthBranch.v ((375759403:ℝ)/168755200) = (763258749723:ℝ)/389061281176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_656
  · change lowerPayment 657 ≤ lowerValue ((point 2 split 4096 657+point 2 split 4096 658)/2)
    have hp : lowerPayment 657 = (93176873901:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 657+point 2 split 4096 658)/2 = (75163533:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75163533:ℝ)/33751040)/ClassicalSixthBranch.v ((75163533:ℝ)/33751040) = (763181436049:ℝ)/389013273288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_657
  · change lowerPayment 658 ≤ lowerValue ((point 2 split 4096 658+point 2 split 4096 659)/2)
    have hp : lowerPayment 658 = (93300919812:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 658+point 2 split 4096 659)/2 = (375875927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375875927:ℝ)/168755200)/ClassicalSixthBranch.v ((375875927:ℝ)/168755200) = (30524164895:ℝ)/15558610616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_658
  · change lowerPayment 659 ≤ lowerValue ((point 2 split 4096 659+point 2 split 4096 660)/2)
    have hp : lowerPayment 659 = (93424922026:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 659+point 2 split 4096 660)/2 = (375934189:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375934189:ℝ)/168755200)/ClassicalSixthBranch.v ((375934189:ℝ)/168755200) = (763026808701:ℝ)/388917257512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_659
  · change lowerPayment 660 ≤ lowerValue ((point 2 split 4096 660+point 2 split 4096 661)/2)
    have hp : lowerPayment 660 = (93548880582:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 660+point 2 split 4096 661)/2 = (375992451:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((375992451:ℝ)/168755200)/ClassicalSixthBranch.v ((375992451:ℝ)/168755200) = (762949495027:ℝ)/388869249624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_660
  · change lowerPayment 661 ≤ lowerValue ((point 2 split 4096 661+point 2 split 4096 662)/2)
    have hp : lowerPayment 661 = (93672795518:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 661+point 2 split 4096 662)/2 = (376050713:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((376050713:ℝ)/168755200)/ClassicalSixthBranch.v ((376050713:ℝ)/168755200) = (762872181353:ℝ)/388821241736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_661
  · change lowerPayment 662 ≤ lowerValue ((point 2 split 4096 662+point 2 split 4096 663)/2)
    have hp : lowerPayment 662 = (93796666872:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 662+point 2 split 4096 663)/2 = (15044359:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15044359:ℝ)/6750208)/ClassicalSixthBranch.v ((15044359:ℝ)/6750208) = (762794867679:ℝ)/388773233848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_662
  · change lowerPayment 663 ≤ lowerValue ((point 2 split 4096 663+point 2 split 4096 664)/2)
    have hp : lowerPayment 663 = (93920494685:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 663+point 2 split 4096 664)/2 = (376167237:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((376167237:ℝ)/168755200)/ClassicalSixthBranch.v ((376167237:ℝ)/168755200) = (152543510801:ℝ)/77745045192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_663
  · change lowerPayment 664 ≤ lowerValue ((point 2 split 4096 664+point 2 split 4096 665)/2)
    have hp : lowerPayment 664 = (94044278995:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 664+point 2 split 4096 665)/2 = (376225499:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((376225499:ℝ)/168755200)/ClassicalSixthBranch.v ((376225499:ℝ)/168755200) = (762640240331:ℝ)/388677218072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_664
  · change lowerPayment 665 ≤ lowerValue ((point 2 split 4096 665+point 2 split 4096 666)/2)
    have hp : lowerPayment 665 = (94168019839:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 665+point 2 split 4096 666)/2 = (376283761:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((376283761:ℝ)/168755200)/ClassicalSixthBranch.v ((376283761:ℝ)/168755200) = (762562926657:ℝ)/388629210184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_665
  · change lowerPayment 666 ≤ lowerValue ((point 2 split 4096 666+point 2 split 4096 667)/2)
    have hp : lowerPayment 666 = (94291717258:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 666+point 2 split 4096 667)/2 = (376342023:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((376342023:ℝ)/168755200)/ClassicalSixthBranch.v ((376342023:ℝ)/168755200) = (762485612983:ℝ)/388581202296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_666
  · change lowerPayment 667 ≤ lowerValue ((point 2 split 4096 667+point 2 split 4096 668)/2)
    have hp : lowerPayment 667 = (94415371289:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 667+point 2 split 4096 668)/2 = (75280057:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75280057:ℝ)/33751040)/ClassicalSixthBranch.v ((75280057:ℝ)/33751040) = (762408299309:ℝ)/388533194408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_667
  · change lowerPayment 668 ≤ lowerValue ((point 2 split 4096 668+point 2 split 4096 669)/2)
    have hp : lowerPayment 668 = (94538981971:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 668+point 2 split 4096 669)/2 = (376458547:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((376458547:ℝ)/168755200)/ClassicalSixthBranch.v ((376458547:ℝ)/168755200) = (152466197127:ℝ)/77697037304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_668
  · change lowerPayment 669 ≤ lowerValue ((point 2 split 4096 669+point 2 split 4096 670)/2)
    have hp : lowerPayment 669 = (94662549343:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 669+point 2 split 4096 670)/2 = (3655503:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((3655503:ℝ)/1638400)/ClassicalSixthBranch.v ((3655503:ℝ)/1638400) = (7400521087:ℝ)/3771234744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_669
  · change lowerPayment 670 ≤ lowerValue ((point 2 split 4096 670+point 2 split 4096 671)/2)
    have hp : lowerPayment 670 = (94786073444:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 670+point 2 split 4096 671)/2 = (376575071:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((376575071:ℝ)/168755200)/ClassicalSixthBranch.v ((376575071:ℝ)/168755200) = (762176358287:ℝ)/388389170744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_670
  · change lowerPayment 671 ≤ lowerValue ((point 2 split 4096 671+point 2 split 4096 672)/2)
    have hp : lowerPayment 671 = (94909554311:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 671+point 2 split 4096 672)/2 = (376633333:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((376633333:ℝ)/168755200)/ClassicalSixthBranch.v ((376633333:ℝ)/168755200) = (762099044613:ℝ)/388341162856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_671
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_041
