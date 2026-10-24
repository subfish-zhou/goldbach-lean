import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints042
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_042 (j : Fin 16) : lowerPayment (16*42+j.val) ≤
    lowerValue ((point 2 split 4096 (16*42+j.val)+point 2 split 4096 (16*42+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 672 ≤ lowerValue ((point 2 split 4096 672+point 2 split 4096 673)/2)
    have hp : lowerPayment 672 = (95032991984:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 672+point 2 split 4096 673)/2 = (75338319:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75338319:ℝ)/33751040)/ClassicalSixthBranch.v ((75338319:ℝ)/33751040) = (762021730939:ℝ)/388293154968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_672
  · change lowerPayment 673 ≤ lowerValue ((point 2 split 4096 673+point 2 split 4096 674)/2)
    have hp : lowerPayment 673 = (95156386500:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 673+point 2 split 4096 674)/2 = (376749857:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((376749857:ℝ)/168755200)/ClassicalSixthBranch.v ((376749857:ℝ)/168755200) = (152388883453:ℝ)/77649029416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_673
  · change lowerPayment 674 ≤ lowerValue ((point 2 split 4096 674+point 2 split 4096 675)/2)
    have hp : lowerPayment 674 = (95279737898:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 674+point 2 split 4096 675)/2 = (376808119:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((376808119:ℝ)/168755200)/ClassicalSixthBranch.v ((376808119:ℝ)/168755200) = (761867103591:ℝ)/388197139192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_674
  · change lowerPayment 675 ≤ lowerValue ((point 2 split 4096 675+point 2 split 4096 676)/2)
    have hp : lowerPayment 675 = (95403046217:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 675+point 2 split 4096 676)/2 = (376866381:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((376866381:ℝ)/168755200)/ClassicalSixthBranch.v ((376866381:ℝ)/168755200) = (761789789917:ℝ)/388149131304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_675
  · change lowerPayment 676 ≤ lowerValue ((point 2 split 4096 676+point 2 split 4096 677)/2)
    have hp : lowerPayment 676 = (95526311495:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 676+point 2 split 4096 677)/2 = (376924643:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((376924643:ℝ)/168755200)/ClassicalSixthBranch.v ((376924643:ℝ)/168755200) = (761712476243:ℝ)/388101123416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_676
  · change lowerPayment 677 ≤ lowerValue ((point 2 split 4096 677+point 2 split 4096 678)/2)
    have hp : lowerPayment 677 = (95649533769:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 677+point 2 split 4096 678)/2 = (75396581:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75396581:ℝ)/33751040)/ClassicalSixthBranch.v ((75396581:ℝ)/33751040) = (761635162569:ℝ)/388053115528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_677
  · change lowerPayment 678 ≤ lowerValue ((point 2 split 4096 678+point 2 split 4096 679)/2)
    have hp : lowerPayment 678 = (95772713080:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 678+point 2 split 4096 679)/2 = (377041167:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377041167:ℝ)/168755200)/ClassicalSixthBranch.v ((377041167:ℝ)/168755200) = (152311569779:ℝ)/77601021528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_678
  · change lowerPayment 679 ≤ lowerValue ((point 2 split 4096 679+point 2 split 4096 680)/2)
    have hp : lowerPayment 679 = (95895849464:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 679+point 2 split 4096 680)/2 = (377099429:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377099429:ℝ)/168755200)/ClassicalSixthBranch.v ((377099429:ℝ)/168755200) = (761480535221:ℝ)/387957099752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_679
  · change lowerPayment 680 ≤ lowerValue ((point 2 split 4096 680+point 2 split 4096 681)/2)
    have hp : lowerPayment 680 = (96018942959:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 680+point 2 split 4096 681)/2 = (377157691:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377157691:ℝ)/168755200)/ClassicalSixthBranch.v ((377157691:ℝ)/168755200) = (761403221547:ℝ)/387909091864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_680
  · change lowerPayment 681 ≤ lowerValue ((point 2 split 4096 681+point 2 split 4096 682)/2)
    have hp : lowerPayment 681 = (96141993605:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 681+point 2 split 4096 682)/2 = (377215953:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377215953:ℝ)/168755200)/ClassicalSixthBranch.v ((377215953:ℝ)/168755200) = (761325907873:ℝ)/387861083976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_681
  · change lowerPayment 682 ≤ lowerValue ((point 2 split 4096 682+point 2 split 4096 683)/2)
    have hp : lowerPayment 682 = (96265001439:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 682+point 2 split 4096 683)/2 = (75454843:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75454843:ℝ)/33751040)/ClassicalSixthBranch.v ((75454843:ℝ)/33751040) = (761248594199:ℝ)/387813076088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_682
  · change lowerPayment 683 ≤ lowerValue ((point 2 split 4096 683+point 2 split 4096 684)/2)
    have hp : lowerPayment 683 = (96387966500:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 683+point 2 split 4096 684)/2 = (377332477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377332477:ℝ)/168755200)/ClassicalSixthBranch.v ((377332477:ℝ)/168755200) = (30446851221:ℝ)/15510602728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_683
  · change lowerPayment 684 ≤ lowerValue ((point 2 split 4096 684+point 2 split 4096 685)/2)
    have hp : lowerPayment 684 = (96510888825:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 684+point 2 split 4096 685)/2 = (377390739:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377390739:ℝ)/168755200)/ClassicalSixthBranch.v ((377390739:ℝ)/168755200) = (761093966851:ℝ)/387717060312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_684
  · change lowerPayment 685 ≤ lowerValue ((point 2 split 4096 685+point 2 split 4096 686)/2)
    have hp : lowerPayment 685 = (96633768452:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 685+point 2 split 4096 686)/2 = (377449001:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377449001:ℝ)/168755200)/ClassicalSixthBranch.v ((377449001:ℝ)/168755200) = (761016653177:ℝ)/387669052424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_685
  · change lowerPayment 686 ≤ lowerValue ((point 2 split 4096 686+point 2 split 4096 687)/2)
    have hp : lowerPayment 686 = (96756605420:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 686+point 2 split 4096 687)/2 = (377507263:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377507263:ℝ)/168755200)/ClassicalSixthBranch.v ((377507263:ℝ)/168755200) = (760939339503:ℝ)/387621044536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_686
  · change lowerPayment 687 ≤ lowerValue ((point 2 split 4096 687+point 2 split 4096 688)/2)
    have hp : lowerPayment 687 = (96879399766:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 687+point 2 split 4096 688)/2 = (15102621:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15102621:ℝ)/6750208)/ClassicalSixthBranch.v ((15102621:ℝ)/6750208) = (760862025829:ℝ)/387573036648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_687
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_042
