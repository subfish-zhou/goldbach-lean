import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints043
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_043 (j : Fin 16) : lowerPayment (16*43+j.val) ≤
    lowerValue ((point 2 split 4096 (16*43+j.val)+point 2 split 4096 (16*43+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 688 ≤ lowerValue ((point 2 split 4096 688+point 2 split 4096 689)/2)
    have hp : lowerPayment 688 = (97002151529:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 688+point 2 split 4096 689)/2 = (377623787:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377623787:ℝ)/168755200)/ClassicalSixthBranch.v ((377623787:ℝ)/168755200) = (152156942431:ℝ)/77505005752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_688
  · change lowerPayment 689 ≤ lowerValue ((point 2 split 4096 689+point 2 split 4096 690)/2)
    have hp : lowerPayment 689 = (97124860746:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 689+point 2 split 4096 690)/2 = (377682049:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377682049:ℝ)/168755200)/ClassicalSixthBranch.v ((377682049:ℝ)/168755200) = (760707398481:ℝ)/387477020872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_689
  · change lowerPayment 690 ≤ lowerValue ((point 2 split 4096 690+point 2 split 4096 691)/2)
    have hp : lowerPayment 690 = (97247527455:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 690+point 2 split 4096 691)/2 = (377740311:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377740311:ℝ)/168755200)/ClassicalSixthBranch.v ((377740311:ℝ)/168755200) = (760630084807:ℝ)/387429012984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_690
  · change lowerPayment 691 ≤ lowerValue ((point 2 split 4096 691+point 2 split 4096 692)/2)
    have hp : lowerPayment 691 = (97370151695:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 691+point 2 split 4096 692)/2 = (377798573:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377798573:ℝ)/168755200)/ClassicalSixthBranch.v ((377798573:ℝ)/168755200) = (760552771133:ℝ)/387381005096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_691
  · change lowerPayment 692 ≤ lowerValue ((point 2 split 4096 692+point 2 split 4096 693)/2)
    have hp : lowerPayment 692 = (97492733502:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 692+point 2 split 4096 693)/2 = (75571367:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75571367:ℝ)/33751040)/ClassicalSixthBranch.v ((75571367:ℝ)/33751040) = (760475457459:ℝ)/387332997208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_692
  · change lowerPayment 693 ≤ lowerValue ((point 2 split 4096 693+point 2 split 4096 694)/2)
    have hp : lowerPayment 693 = (97615272915:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 693+point 2 split 4096 694)/2 = (377915097:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377915097:ℝ)/168755200)/ClassicalSixthBranch.v ((377915097:ℝ)/168755200) = (152079628757:ℝ)/77456997864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_693
  · change lowerPayment 694 ≤ lowerValue ((point 2 split 4096 694+point 2 split 4096 695)/2)
    have hp : lowerPayment 694 = (97737769972:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 694+point 2 split 4096 695)/2 = (377973359:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((377973359:ℝ)/168755200)/ClassicalSixthBranch.v ((377973359:ℝ)/168755200) = (760320830111:ℝ)/387236981432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_694
  · change lowerPayment 695 ≤ lowerValue ((point 2 split 4096 695+point 2 split 4096 696)/2)
    have hp : lowerPayment 695 = (97860224710:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 695+point 2 split 4096 696)/2 = (378031621:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378031621:ℝ)/168755200)/ClassicalSixthBranch.v ((378031621:ℝ)/168755200) = (760243516437:ℝ)/387188973544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_695
  · change lowerPayment 696 ≤ lowerValue ((point 2 split 4096 696+point 2 split 4096 697)/2)
    have hp : lowerPayment 696 = (97982637167:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 696+point 2 split 4096 697)/2 = (378089883:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378089883:ℝ)/168755200)/ClassicalSixthBranch.v ((378089883:ℝ)/168755200) = (760166202763:ℝ)/387140965656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_696
  · change lowerPayment 697 ≤ lowerValue ((point 2 split 4096 697+point 2 split 4096 698)/2)
    have hp : lowerPayment 697 = (98105007380:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 697+point 2 split 4096 698)/2 = (75629629:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75629629:ℝ)/33751040)/ClassicalSixthBranch.v ((75629629:ℝ)/33751040) = (760088889089:ℝ)/387092957768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_697
  · change lowerPayment 698 ≤ lowerValue ((point 2 split 4096 698+point 2 split 4096 699)/2)
    have hp : lowerPayment 698 = (98227335388:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 698+point 2 split 4096 699)/2 = (378206407:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378206407:ℝ)/168755200)/ClassicalSixthBranch.v ((378206407:ℝ)/168755200) = (152002315083:ℝ)/77408989976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_698
  · change lowerPayment 699 ≤ lowerValue ((point 2 split 4096 699+point 2 split 4096 700)/2)
    have hp : lowerPayment 699 = (98349621228:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 699+point 2 split 4096 700)/2 = (378264669:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378264669:ℝ)/168755200)/ClassicalSixthBranch.v ((378264669:ℝ)/168755200) = (759934261741:ℝ)/386996941992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_699
  · change lowerPayment 700 ≤ lowerValue ((point 2 split 4096 700+point 2 split 4096 701)/2)
    have hp : lowerPayment 700 = (98471864937:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 700+point 2 split 4096 701)/2 = (378322931:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378322931:ℝ)/168755200)/ClassicalSixthBranch.v ((378322931:ℝ)/168755200) = (759856948067:ℝ)/386948934104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_700
  · change lowerPayment 701 ≤ lowerValue ((point 2 split 4096 701+point 2 split 4096 702)/2)
    have hp : lowerPayment 701 = (98594066553:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 701+point 2 split 4096 702)/2 = (378381193:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378381193:ℝ)/168755200)/ClassicalSixthBranch.v ((378381193:ℝ)/168755200) = (759779634393:ℝ)/386900926216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_701
  · change lowerPayment 702 ≤ lowerValue ((point 2 split 4096 702+point 2 split 4096 703)/2)
    have hp : lowerPayment 702 = (98716226114:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 702+point 2 split 4096 703)/2 = (75687891:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75687891:ℝ)/33751040)/ClassicalSixthBranch.v ((75687891:ℝ)/33751040) = (759702320719:ℝ)/386852918328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_702
  · change lowerPayment 703 ≤ lowerValue ((point 2 split 4096 703+point 2 split 4096 704)/2)
    have hp : lowerPayment 703 = (98838343656:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 703+point 2 split 4096 704)/2 = (378497717:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378497717:ℝ)/168755200)/ClassicalSixthBranch.v ((378497717:ℝ)/168755200) = (151925001409:ℝ)/77360982088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_703
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_043
