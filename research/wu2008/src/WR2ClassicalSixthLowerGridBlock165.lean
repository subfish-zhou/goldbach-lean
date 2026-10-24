import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints165
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_165 (j : Fin 16) : lowerPayment (16*165+j.val) ≤
    lowerValue ((point 2 split 4096 (16*165+j.val)+point 2 split 4096 (16*165+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2640 ≤ lowerValue ((point 2 split 4096 2640+point 2 split 4096 2641)/2)
    have hp : lowerPayment 2640 = (289608493271:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2640+point 2 split 4096 2641)/2 = (491351211:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491351211:ℝ)/168755200)/ClassicalSixthBranch.v ((491351211:ℝ)/168755200) = (609868420507:ℝ)/293813631384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2640
  · change lowerPayment 2641 ≤ lowerValue ((point 2 split 4096 2641+point 2 split 4096 2642)/2)
    have hp : lowerPayment 2641 = (289696252838:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2641+point 2 split 4096 2642)/2 = (491409473:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491409473:ℝ)/168755200)/ClassicalSixthBranch.v ((491409473:ℝ)/168755200) = (609791106833:ℝ)/293765623496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2641
  · change lowerPayment 2642 ≤ lowerValue ((point 2 split 4096 2642+point 2 split 4096 2643)/2)
    have hp : lowerPayment 2642 = (289784011982:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2642+point 2 split 4096 2643)/2 = (98293547:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98293547:ℝ)/33751040)/ClassicalSixthBranch.v ((98293547:ℝ)/33751040) = (609713793159:ℝ)/293717615608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2642
  · change lowerPayment 2643 ≤ lowerValue ((point 2 split 4096 2643+point 2 split 4096 2644)/2)
    have hp : lowerPayment 2643 = (289871770718:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2643+point 2 split 4096 2644)/2 = (491525997:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491525997:ℝ)/168755200)/ClassicalSixthBranch.v ((491525997:ℝ)/168755200) = (121927295897:ℝ)/58733921544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2643
  · change lowerPayment 2644 ≤ lowerValue ((point 2 split 4096 2644+point 2 split 4096 2645)/2)
    have hp : lowerPayment 2644 = (289959529060:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2644+point 2 split 4096 2645)/2 = (491584259:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491584259:ℝ)/168755200)/ClassicalSixthBranch.v ((491584259:ℝ)/168755200) = (609559165811:ℝ)/293621599832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2644
  · change lowerPayment 2645 ≤ lowerValue ((point 2 split 4096 2645+point 2 split 4096 2646)/2)
    have hp : lowerPayment 2645 = (290047287022:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2645+point 2 split 4096 2646)/2 = (491642521:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491642521:ℝ)/168755200)/ClassicalSixthBranch.v ((491642521:ℝ)/168755200) = (609481852137:ℝ)/293573591944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2645
  · change lowerPayment 2646 ≤ lowerValue ((point 2 split 4096 2646+point 2 split 4096 2647)/2)
    have hp : lowerPayment 2646 = (290135044618:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2646+point 2 split 4096 2647)/2 = (491700783:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491700783:ℝ)/168755200)/ClassicalSixthBranch.v ((491700783:ℝ)/168755200) = (609404538463:ℝ)/293525584056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2646
  · change lowerPayment 2647 ≤ lowerValue ((point 2 split 4096 2647+point 2 split 4096 2648)/2)
    have hp : lowerPayment 2647 = (290222801862:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2647+point 2 split 4096 2648)/2 = (98351809:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98351809:ℝ)/33751040)/ClassicalSixthBranch.v ((98351809:ℝ)/33751040) = (609327224789:ℝ)/293477576168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2647
  · change lowerPayment 2648 ≤ lowerValue ((point 2 split 4096 2648+point 2 split 4096 2649)/2)
    have hp : lowerPayment 2648 = (290310558770:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2648+point 2 split 4096 2649)/2 = (491817307:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491817307:ℝ)/168755200)/ClassicalSixthBranch.v ((491817307:ℝ)/168755200) = (121849982223:ℝ)/58685913656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2648
  · change lowerPayment 2649 ≤ lowerValue ((point 2 split 4096 2649+point 2 split 4096 2650)/2)
    have hp : lowerPayment 2649 = (290398315354:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2649+point 2 split 4096 2650)/2 = (491875569:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491875569:ℝ)/168755200)/ClassicalSixthBranch.v ((491875569:ℝ)/168755200) = (609172597441:ℝ)/293381560392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2649
  · change lowerPayment 2650 ≤ lowerValue ((point 2 split 4096 2650+point 2 split 4096 2651)/2)
    have hp : lowerPayment 2650 = (290486071630:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2650+point 2 split 4096 2651)/2 = (491933831:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491933831:ℝ)/168755200)/ClassicalSixthBranch.v ((491933831:ℝ)/168755200) = (609095283767:ℝ)/293333552504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2650
  · change lowerPayment 2651 ≤ lowerValue ((point 2 split 4096 2651+point 2 split 4096 2652)/2)
    have hp : lowerPayment 2651 = (290573827612:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2651+point 2 split 4096 2652)/2 = (491992093:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((491992093:ℝ)/168755200)/ClassicalSixthBranch.v ((491992093:ℝ)/168755200) = (609017970093:ℝ)/293285544616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2651
  · change lowerPayment 2652 ≤ lowerValue ((point 2 split 4096 2652+point 2 split 4096 2653)/2)
    have hp : lowerPayment 2652 = (290661583313:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2652+point 2 split 4096 2653)/2 = (98410071:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98410071:ℝ)/33751040)/ClassicalSixthBranch.v ((98410071:ℝ)/33751040) = (608940656419:ℝ)/293237536728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2652
  · change lowerPayment 2653 ≤ lowerValue ((point 2 split 4096 2653+point 2 split 4096 2654)/2)
    have hp : lowerPayment 2653 = (290749338749:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2653+point 2 split 4096 2654)/2 = (492108617:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492108617:ℝ)/168755200)/ClassicalSixthBranch.v ((492108617:ℝ)/168755200) = (121772668549:ℝ)/58637905768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2653
  · change lowerPayment 2654 ≤ lowerValue ((point 2 split 4096 2654+point 2 split 4096 2655)/2)
    have hp : lowerPayment 2654 = (290837093933:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2654+point 2 split 4096 2655)/2 = (492166879:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492166879:ℝ)/168755200)/ClassicalSixthBranch.v ((492166879:ℝ)/168755200) = (608786029071:ℝ)/293141520952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2654
  · change lowerPayment 2655 ≤ lowerValue ((point 2 split 4096 2655+point 2 split 4096 2656)/2)
    have hp : lowerPayment 2655 = (290924848879:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2655+point 2 split 4096 2656)/2 = (492225141:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((492225141:ℝ)/168755200)/ClassicalSixthBranch.v ((492225141:ℝ)/168755200) = (608708715397:ℝ)/293093513064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2655
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_165
