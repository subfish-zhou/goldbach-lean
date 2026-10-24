import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints162
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_162 (j : Fin 16) : lowerPayment (16*162+j.val) ≤
    lowerValue ((point 2 split 4096 (16*162+j.val)+point 2 split 4096 (16*162+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2592 ≤ lowerValue ((point 2 split 4096 2592+point 2 split 4096 2593)/2)
    have hp : lowerPayment 2592 = (285395257029:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2592+point 2 split 4096 2593)/2 = (97710927:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97710927:ℝ)/33751040)/ClassicalSixthBranch.v ((97710927:ℝ)/33751040) = (613579476859:ℝ)/296118010008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2592
  · change lowerPayment 2593 ≤ lowerValue ((point 2 split 4096 2593+point 2 split 4096 2594)/2)
    have hp : lowerPayment 2593 = (285483053688:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2593+point 2 split 4096 2594)/2 = (488612897:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488612897:ℝ)/168755200)/ClassicalSixthBranch.v ((488612897:ℝ)/168755200) = (122700432637:ℝ)/59214000424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2593
  · change lowerPayment 2594 ≤ lowerValue ((point 2 split 4096 2594+point 2 split 4096 2595)/2)
    have hp : lowerPayment 2594 = (285570849238:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2594+point 2 split 4096 2595)/2 = (488671159:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488671159:ℝ)/168755200)/ClassicalSixthBranch.v ((488671159:ℝ)/168755200) = (613424849511:ℝ)/296021994232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2594
  · change lowerPayment 2595 ≤ lowerValue ((point 2 split 4096 2595+point 2 split 4096 2596)/2)
    have hp : lowerPayment 2595 = (285658643694:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2595+point 2 split 4096 2596)/2 = (488729421:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488729421:ℝ)/168755200)/ClassicalSixthBranch.v ((488729421:ℝ)/168755200) = (613347535837:ℝ)/295973986344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2595
  · change lowerPayment 2596 ≤ lowerValue ((point 2 split 4096 2596+point 2 split 4096 2597)/2)
    have hp : lowerPayment 2596 = (285746437069:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2596+point 2 split 4096 2597)/2 = (488787683:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488787683:ℝ)/168755200)/ClassicalSixthBranch.v ((488787683:ℝ)/168755200) = (613270222163:ℝ)/295925978456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2596
  · change lowerPayment 2597 ≤ lowerValue ((point 2 split 4096 2597+point 2 split 4096 2598)/2)
    have hp : lowerPayment 2597 = (285834229377:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2597+point 2 split 4096 2598)/2 = (97769189:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97769189:ℝ)/33751040)/ClassicalSixthBranch.v ((97769189:ℝ)/33751040) = (613192908489:ℝ)/295877970568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2597
  · change lowerPayment 2598 ≤ lowerValue ((point 2 split 4096 2598+point 2 split 4096 2599)/2)
    have hp : lowerPayment 2598 = (285922020635:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2598+point 2 split 4096 2599)/2 = (488904207:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488904207:ℝ)/168755200)/ClassicalSixthBranch.v ((488904207:ℝ)/168755200) = (122623118963:ℝ)/59165992536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2598
  · change lowerPayment 2599 ≤ lowerValue ((point 2 split 4096 2599+point 2 split 4096 2600)/2)
    have hp : lowerPayment 2599 = (286009810854:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2599+point 2 split 4096 2600)/2 = (488962469:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((488962469:ℝ)/168755200)/ClassicalSixthBranch.v ((488962469:ℝ)/168755200) = (613038281141:ℝ)/295781954792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2599
  · change lowerPayment 2600 ≤ lowerValue ((point 2 split 4096 2600+point 2 split 4096 2601)/2)
    have hp : lowerPayment 2600 = (286097600051:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2600+point 2 split 4096 2601)/2 = (489020731:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489020731:ℝ)/168755200)/ClassicalSixthBranch.v ((489020731:ℝ)/168755200) = (612960967467:ℝ)/295733946904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2600
  · change lowerPayment 2601 ≤ lowerValue ((point 2 split 4096 2601+point 2 split 4096 2602)/2)
    have hp : lowerPayment 2601 = (286185388238:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2601+point 2 split 4096 2602)/2 = (489078993:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489078993:ℝ)/168755200)/ClassicalSixthBranch.v ((489078993:ℝ)/168755200) = (612883653793:ℝ)/295685939016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2601
  · change lowerPayment 2602 ≤ lowerValue ((point 2 split 4096 2602+point 2 split 4096 2603)/2)
    have hp : lowerPayment 2602 = (286273175432:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2602+point 2 split 4096 2603)/2 = (97827451:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97827451:ℝ)/33751040)/ClassicalSixthBranch.v ((97827451:ℝ)/33751040) = (612806340119:ℝ)/295637931128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2602
  · change lowerPayment 2603 ≤ lowerValue ((point 2 split 4096 2603+point 2 split 4096 2604)/2)
    have hp : lowerPayment 2603 = (286360961645:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2603+point 2 split 4096 2604)/2 = (489195517:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489195517:ℝ)/168755200)/ClassicalSixthBranch.v ((489195517:ℝ)/168755200) = (122545805289:ℝ)/59117984648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2603
  · change lowerPayment 2604 ≤ lowerValue ((point 2 split 4096 2604+point 2 split 4096 2605)/2)
    have hp : lowerPayment 2604 = (286448746892:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2604+point 2 split 4096 2605)/2 = (489253779:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489253779:ℝ)/168755200)/ClassicalSixthBranch.v ((489253779:ℝ)/168755200) = (612651712771:ℝ)/295541915352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2604
  · change lowerPayment 2605 ≤ lowerValue ((point 2 split 4096 2605+point 2 split 4096 2606)/2)
    have hp : lowerPayment 2605 = (286536531188:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2605+point 2 split 4096 2606)/2 = (489312041:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489312041:ℝ)/168755200)/ClassicalSixthBranch.v ((489312041:ℝ)/168755200) = (612574399097:ℝ)/295493907464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2605
  · change lowerPayment 2606 ≤ lowerValue ((point 2 split 4096 2606+point 2 split 4096 2607)/2)
    have hp : lowerPayment 2606 = (286624314547:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2606+point 2 split 4096 2607)/2 = (489370303:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((489370303:ℝ)/168755200)/ClassicalSixthBranch.v ((489370303:ℝ)/168755200) = (612497085423:ℝ)/295445899576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2606
  · change lowerPayment 2607 ≤ lowerValue ((point 2 split 4096 2607+point 2 split 4096 2608)/2)
    have hp : lowerPayment 2607 = (286712096983:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2607+point 2 split 4096 2608)/2 = (97885713:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((97885713:ℝ)/33751040)/ClassicalSixthBranch.v ((97885713:ℝ)/33751040) = (612419771749:ℝ)/295397891688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2607
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_162
