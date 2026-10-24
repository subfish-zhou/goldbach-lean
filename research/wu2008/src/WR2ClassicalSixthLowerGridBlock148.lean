import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints148
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_148 (j : Fin 16) : lowerPayment (16*148+j.val) ≤
    lowerValue ((point 2 split 4096 (16*148+j.val)+point 2 split 4096 (16*148+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2368 ≤ lowerValue ((point 2 split 4096 2368+point 2 split 4096 2369)/2)
    have hp : lowerPayment 2368 = (265673407718:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2368+point 2 split 4096 2369)/2 = (475503947:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475503947:ℝ)/168755200)/ClassicalSixthBranch.v ((475503947:ℝ)/168755200) = (126179547967:ℝ)/61374355384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2368
  · change lowerPayment 2369 ≤ lowerValue ((point 2 split 4096 2369+point 2 split 4096 2370)/2)
    have hp : lowerPayment 2369 = (265761818304:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2369+point 2 split 4096 2370)/2 = (475562209:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475562209:ℝ)/168755200)/ClassicalSixthBranch.v ((475562209:ℝ)/168755200) = (630820426161:ℝ)/306823769032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2369
  · change lowerPayment 2370 ≤ lowerValue ((point 2 split 4096 2370+point 2 split 4096 2371)/2)
    have hp : lowerPayment 2370 = (265850224510:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2370+point 2 split 4096 2371)/2 = (475620471:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475620471:ℝ)/168755200)/ClassicalSixthBranch.v ((475620471:ℝ)/168755200) = (630743112487:ℝ)/306775761144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2370
  · change lowerPayment 2371 ≤ lowerValue ((point 2 split 4096 2371+point 2 split 4096 2372)/2)
    have hp : lowerPayment 2371 = (265938626352:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2371+point 2 split 4096 2372)/2 = (475678733:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475678733:ℝ)/168755200)/ClassicalSixthBranch.v ((475678733:ℝ)/168755200) = (630665798813:ℝ)/306727753256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2371
  · change lowerPayment 2372 ≤ lowerValue ((point 2 split 4096 2372+point 2 split 4096 2373)/2)
    have hp : lowerPayment 2372 = (266027023845:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2372+point 2 split 4096 2373)/2 = (95147399:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95147399:ℝ)/33751040)/ClassicalSixthBranch.v ((95147399:ℝ)/33751040) = (630588485139:ℝ)/306679745368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2372
  · change lowerPayment 2373 ≤ lowerValue ((point 2 split 4096 2373+point 2 split 4096 2374)/2)
    have hp : lowerPayment 2373 = (266115417003:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2373+point 2 split 4096 2374)/2 = (475795257:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475795257:ℝ)/168755200)/ClassicalSixthBranch.v ((475795257:ℝ)/168755200) = (126102234293:ℝ)/61326347496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2373
  · change lowerPayment 2374 ≤ lowerValue ((point 2 split 4096 2374+point 2 split 4096 2375)/2)
    have hp : lowerPayment 2374 = (266203805841:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2374+point 2 split 4096 2375)/2 = (475853519:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475853519:ℝ)/168755200)/ClassicalSixthBranch.v ((475853519:ℝ)/168755200) = (630433857791:ℝ)/306583729592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2374
  · change lowerPayment 2375 ≤ lowerValue ((point 2 split 4096 2375+point 2 split 4096 2376)/2)
    have hp : lowerPayment 2375 = (266292190375:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2375+point 2 split 4096 2376)/2 = (475911781:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475911781:ℝ)/168755200)/ClassicalSixthBranch.v ((475911781:ℝ)/168755200) = (630356544117:ℝ)/306535721704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2375
  · change lowerPayment 2376 ≤ lowerValue ((point 2 split 4096 2376+point 2 split 4096 2377)/2)
    have hp : lowerPayment 2376 = (266380570618:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2376+point 2 split 4096 2377)/2 = (475970043:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((475970043:ℝ)/168755200)/ClassicalSixthBranch.v ((475970043:ℝ)/168755200) = (630279230443:ℝ)/306487713816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2376
  · change lowerPayment 2377 ≤ lowerValue ((point 2 split 4096 2377+point 2 split 4096 2378)/2)
    have hp : lowerPayment 2377 = (266468946587:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2377+point 2 split 4096 2378)/2 = (95205661:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95205661:ℝ)/33751040)/ClassicalSixthBranch.v ((95205661:ℝ)/33751040) = (630201916769:ℝ)/306439705928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2377
  · change lowerPayment 2378 ≤ lowerValue ((point 2 split 4096 2378+point 2 split 4096 2379)/2)
    have hp : lowerPayment 2378 = (266557318296:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2378+point 2 split 4096 2379)/2 = (476086567:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476086567:ℝ)/168755200)/ClassicalSixthBranch.v ((476086567:ℝ)/168755200) = (126024920619:ℝ)/61278339608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2378
  · change lowerPayment 2379 ≤ lowerValue ((point 2 split 4096 2379+point 2 split 4096 2380)/2)
    have hp : lowerPayment 2379 = (266645685759:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2379+point 2 split 4096 2380)/2 = (476144829:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476144829:ℝ)/168755200)/ClassicalSixthBranch.v ((476144829:ℝ)/168755200) = (630047289421:ℝ)/306343690152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2379
  · change lowerPayment 2380 ≤ lowerValue ((point 2 split 4096 2380+point 2 split 4096 2381)/2)
    have hp : lowerPayment 2380 = (266734048992:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2380+point 2 split 4096 2381)/2 = (476203091:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476203091:ℝ)/168755200)/ClassicalSixthBranch.v ((476203091:ℝ)/168755200) = (629969975747:ℝ)/306295682264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2380
  · change lowerPayment 2381 ≤ lowerValue ((point 2 split 4096 2381+point 2 split 4096 2382)/2)
    have hp : lowerPayment 2381 = (266822408010:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2381+point 2 split 4096 2382)/2 = (476261353:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476261353:ℝ)/168755200)/ClassicalSixthBranch.v ((476261353:ℝ)/168755200) = (629892662073:ℝ)/306247674376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2381
  · change lowerPayment 2382 ≤ lowerValue ((point 2 split 4096 2382+point 2 split 4096 2383)/2)
    have hp : lowerPayment 2382 = (266910762827:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2382+point 2 split 4096 2383)/2 = (95263923:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95263923:ℝ)/33751040)/ClassicalSixthBranch.v ((95263923:ℝ)/33751040) = (629815348399:ℝ)/306199666488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2382
  · change lowerPayment 2383 ≤ lowerValue ((point 2 split 4096 2383+point 2 split 4096 2384)/2)
    have hp : lowerPayment 2383 = (266999113459:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2383+point 2 split 4096 2384)/2 = (476377877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((476377877:ℝ)/168755200)/ClassicalSixthBranch.v ((476377877:ℝ)/168755200) = (25189521389:ℝ)/12246066344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2383
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_148
