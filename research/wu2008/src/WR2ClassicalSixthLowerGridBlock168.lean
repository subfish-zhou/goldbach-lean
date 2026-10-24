import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints168
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_168 (j : Fin 16) : lowerPayment (16*168+j.val) ≤
    lowerValue ((point 2 split 4096 (16*168+j.val)+point 2 split 4096 (16*168+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2688 ≤ lowerValue ((point 2 split 4096 2688+point 2 split 4096 2689)/2)
    have hp : lowerPayment 2688 = (293820722069:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2688+point 2 split 4096 2689)/2 = (494147787:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494147787:ℝ)/168755200)/ClassicalSixthBranch.v ((494147787:ℝ)/168755200) = (121231472831:ℝ)/58301850552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2688
  · change lowerPayment 2689 ≤ lowerValue ((point 2 split 4096 2689+point 2 split 4096 2690)/2)
    have hp : lowerPayment 2689 = (293908477410:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2689+point 2 split 4096 2690)/2 = (494206049:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494206049:ℝ)/168755200)/ClassicalSixthBranch.v ((494206049:ℝ)/168755200) = (606080050481:ℝ)/291461244872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2689
  · change lowerPayment 2690 ≤ lowerValue ((point 2 split 4096 2690+point 2 split 4096 2691)/2)
    have hp : lowerPayment 2690 = (293996233010:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2690+point 2 split 4096 2691)/2 = (494264311:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494264311:ℝ)/168755200)/ClassicalSixthBranch.v ((494264311:ℝ)/168755200) = (606002736807:ℝ)/291413236984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2690
  · change lowerPayment 2691 ≤ lowerValue ((point 2 split 4096 2691+point 2 split 4096 2692)/2)
    have hp : lowerPayment 2691 = (294083988885:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2691+point 2 split 4096 2692)/2 = (494322573:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494322573:ℝ)/168755200)/ClassicalSixthBranch.v ((494322573:ℝ)/168755200) = (605925423133:ℝ)/291365229096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2691
  · change lowerPayment 2692 ≤ lowerValue ((point 2 split 4096 2692+point 2 split 4096 2693)/2)
    have hp : lowerPayment 2692 = (294171745049:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2692+point 2 split 4096 2693)/2 = (98876167:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98876167:ℝ)/33751040)/ClassicalSixthBranch.v ((98876167:ℝ)/33751040) = (605848109459:ℝ)/291317221208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2692
  · change lowerPayment 2693 ≤ lowerValue ((point 2 split 4096 2693+point 2 split 4096 2694)/2)
    have hp : lowerPayment 2693 = (294259501516:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2693+point 2 split 4096 2694)/2 = (494439097:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494439097:ℝ)/168755200)/ClassicalSixthBranch.v ((494439097:ℝ)/168755200) = (121154159157:ℝ)/58253842664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2693
  · change lowerPayment 2694 ≤ lowerValue ((point 2 split 4096 2694+point 2 split 4096 2695)/2)
    have hp : lowerPayment 2694 = (294347258300:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2694+point 2 split 4096 2695)/2 = (494497359:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494497359:ℝ)/168755200)/ClassicalSixthBranch.v ((494497359:ℝ)/168755200) = (605693482111:ℝ)/291221205432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2694
  · change lowerPayment 2695 ≤ lowerValue ((point 2 split 4096 2695+point 2 split 4096 2696)/2)
    have hp : lowerPayment 2695 = (294435015415:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2695+point 2 split 4096 2696)/2 = (494555621:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494555621:ℝ)/168755200)/ClassicalSixthBranch.v ((494555621:ℝ)/168755200) = (605616168437:ℝ)/291173197544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2695
  · change lowerPayment 2696 ≤ lowerValue ((point 2 split 4096 2696+point 2 split 4096 2697)/2)
    have hp : lowerPayment 2696 = (294522772876:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2696+point 2 split 4096 2697)/2 = (494613883:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494613883:ℝ)/168755200)/ClassicalSixthBranch.v ((494613883:ℝ)/168755200) = (605538854763:ℝ)/291125189656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2696
  · change lowerPayment 2697 ≤ lowerValue ((point 2 split 4096 2697+point 2 split 4096 2698)/2)
    have hp : lowerPayment 2697 = (294610530696:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2697+point 2 split 4096 2698)/2 = (98934429:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98934429:ℝ)/33751040)/ClassicalSixthBranch.v ((98934429:ℝ)/33751040) = (605461541089:ℝ)/291077181768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2697
  · change lowerPayment 2698 ≤ lowerValue ((point 2 split 4096 2698+point 2 split 4096 2699)/2)
    have hp : lowerPayment 2698 = (294698288890:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2698+point 2 split 4096 2699)/2 = (494730407:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494730407:ℝ)/168755200)/ClassicalSixthBranch.v ((494730407:ℝ)/168755200) = (121076845483:ℝ)/58205834776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2698
  · change lowerPayment 2699 ≤ lowerValue ((point 2 split 4096 2699+point 2 split 4096 2700)/2)
    have hp : lowerPayment 2699 = (294786047473:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2699+point 2 split 4096 2700)/2 = (494788669:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494788669:ℝ)/168755200)/ClassicalSixthBranch.v ((494788669:ℝ)/168755200) = (605306913741:ℝ)/290981165992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2699
  · change lowerPayment 2700 ≤ lowerValue ((point 2 split 4096 2700+point 2 split 4096 2701)/2)
    have hp : lowerPayment 2700 = (294873806457:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2700+point 2 split 4096 2701)/2 = (494846931:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494846931:ℝ)/168755200)/ClassicalSixthBranch.v ((494846931:ℝ)/168755200) = (605229600067:ℝ)/290933158104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2700
  · change lowerPayment 2701 ≤ lowerValue ((point 2 split 4096 2701+point 2 split 4096 2702)/2)
    have hp : lowerPayment 2701 = (294961565858:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2701+point 2 split 4096 2702)/2 = (494905193:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((494905193:ℝ)/168755200)/ClassicalSixthBranch.v ((494905193:ℝ)/168755200) = (605152286393:ℝ)/290885150216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2701
  · change lowerPayment 2702 ≤ lowerValue ((point 2 split 4096 2702+point 2 split 4096 2703)/2)
    have hp : lowerPayment 2702 = (295049325690:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2702+point 2 split 4096 2703)/2 = (98992691:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((98992691:ℝ)/33751040)/ClassicalSixthBranch.v ((98992691:ℝ)/33751040) = (605074972719:ℝ)/290837142328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2702
  · change lowerPayment 2703 ≤ lowerValue ((point 2 split 4096 2703+point 2 split 4096 2704)/2)
    have hp : lowerPayment 2703 = (295137085967:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2703+point 2 split 4096 2704)/2 = (495021717:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((495021717:ℝ)/168755200)/ClassicalSixthBranch.v ((495021717:ℝ)/168755200) = (120999531809:ℝ)/58157826888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2703
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_168
