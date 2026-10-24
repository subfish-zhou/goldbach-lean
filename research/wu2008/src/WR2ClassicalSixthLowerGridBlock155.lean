import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints155
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_155 (j : Fin 16) : lowerPayment (16*155+j.val) ≤
    lowerValue ((point 2 split 4096 (16*155+j.val)+point 2 split 4096 (16*155+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2480 ≤ lowerValue ((point 2 split 4096 2480+point 2 split 4096 2481)/2)
    have hp : lowerPayment 2480 = (275551551179:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2480+point 2 split 4096 2481)/2 = (482029291:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482029291:ℝ)/168755200)/ClassicalSixthBranch.v ((482029291:ℝ)/168755200) = (622238608347:ℝ)/301494893464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2480
  · change lowerPayment 2481 ≤ lowerValue ((point 2 split 4096 2481+point 2 split 4096 2482)/2)
    have hp : lowerPayment 2481 = (275639563275:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2481+point 2 split 4096 2482)/2 = (482087553:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482087553:ℝ)/168755200)/ClassicalSixthBranch.v ((482087553:ℝ)/168755200) = (622161294673:ℝ)/301446885576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2481
  · change lowerPayment 2482 ≤ lowerValue ((point 2 split 4096 2482+point 2 split 4096 2483)/2)
    have hp : lowerPayment 2482 = (275727572643:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2482+point 2 split 4096 2483)/2 = (96429163:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96429163:ℝ)/33751040)/ClassicalSixthBranch.v ((96429163:ℝ)/33751040) = (622083980999:ℝ)/301398877688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2482
  · change lowerPayment 2483 ≤ lowerValue ((point 2 split 4096 2483+point 2 split 4096 2484)/2)
    have hp : lowerPayment 2483 = (275815579297:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2483+point 2 split 4096 2484)/2 = (482204077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482204077:ℝ)/168755200)/ClassicalSixthBranch.v ((482204077:ℝ)/168755200) = (24880266693:ℝ)/12054034792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2483
  · change lowerPayment 2484 ≤ lowerValue ((point 2 split 4096 2484+point 2 split 4096 2485)/2)
    have hp : lowerPayment 2484 = (275903583253:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2484+point 2 split 4096 2485)/2 = (482262339:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482262339:ℝ)/168755200)/ClassicalSixthBranch.v ((482262339:ℝ)/168755200) = (621929353651:ℝ)/301302861912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2484
  · change lowerPayment 2485 ≤ lowerValue ((point 2 split 4096 2485+point 2 split 4096 2486)/2)
    have hp : lowerPayment 2485 = (275991584524:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2485+point 2 split 4096 2486)/2 = (482320601:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482320601:ℝ)/168755200)/ClassicalSixthBranch.v ((482320601:ℝ)/168755200) = (621852039977:ℝ)/301254854024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2485
  · change lowerPayment 2486 ≤ lowerValue ((point 2 split 4096 2486+point 2 split 4096 2487)/2)
    have hp : lowerPayment 2486 = (276079583125:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2486+point 2 split 4096 2487)/2 = (482378863:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482378863:ℝ)/168755200)/ClassicalSixthBranch.v ((482378863:ℝ)/168755200) = (621774726303:ℝ)/301206846136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2486
  · change lowerPayment 2487 ≤ lowerValue ((point 2 split 4096 2487+point 2 split 4096 2488)/2)
    have hp : lowerPayment 2487 = (276167579072:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2487+point 2 split 4096 2488)/2 = (19297485:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19297485:ℝ)/6750208)/ClassicalSixthBranch.v ((19297485:ℝ)/6750208) = (621697412629:ℝ)/301158838248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2487
  · change lowerPayment 2488 ≤ lowerValue ((point 2 split 4096 2488+point 2 split 4096 2489)/2)
    have hp : lowerPayment 2488 = (276255572377:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2488+point 2 split 4096 2489)/2 = (482495387:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482495387:ℝ)/168755200)/ClassicalSixthBranch.v ((482495387:ℝ)/168755200) = (124324019791:ℝ)/60222166072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2488
  · change lowerPayment 2489 ≤ lowerValue ((point 2 split 4096 2489+point 2 split 4096 2490)/2)
    have hp : lowerPayment 2489 = (276343563057:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2489+point 2 split 4096 2490)/2 = (482553649:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482553649:ℝ)/168755200)/ClassicalSixthBranch.v ((482553649:ℝ)/168755200) = (621542785281:ℝ)/301062822472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2489
  · change lowerPayment 2490 ≤ lowerValue ((point 2 split 4096 2490+point 2 split 4096 2491)/2)
    have hp : lowerPayment 2490 = (276431551125:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2490+point 2 split 4096 2491)/2 = (482611911:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482611911:ℝ)/168755200)/ClassicalSixthBranch.v ((482611911:ℝ)/168755200) = (621465471607:ℝ)/301014814584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2490
  · change lowerPayment 2491 ≤ lowerValue ((point 2 split 4096 2491+point 2 split 4096 2492)/2)
    have hp : lowerPayment 2491 = (276519536596:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2491+point 2 split 4096 2492)/2 = (482670173:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482670173:ℝ)/168755200)/ClassicalSixthBranch.v ((482670173:ℝ)/168755200) = (621388157933:ℝ)/300966806696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2491
  · change lowerPayment 2492 ≤ lowerValue ((point 2 split 4096 2492+point 2 split 4096 2493)/2)
    have hp : lowerPayment 2492 = (276607519485:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2492+point 2 split 4096 2493)/2 = (96545687:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96545687:ℝ)/33751040)/ClassicalSixthBranch.v ((96545687:ℝ)/33751040) = (621310844259:ℝ)/300918798808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2492
  · change lowerPayment 2493 ≤ lowerValue ((point 2 split 4096 2493+point 2 split 4096 2494)/2)
    have hp : lowerPayment 2493 = (276695499806:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2493+point 2 split 4096 2494)/2 = (482786697:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482786697:ℝ)/168755200)/ClassicalSixthBranch.v ((482786697:ℝ)/168755200) = (124246706117:ℝ)/60174158184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2493
  · change lowerPayment 2494 ≤ lowerValue ((point 2 split 4096 2494+point 2 split 4096 2495)/2)
    have hp : lowerPayment 2494 = (276783477574:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2494+point 2 split 4096 2495)/2 = (482844959:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482844959:ℝ)/168755200)/ClassicalSixthBranch.v ((482844959:ℝ)/168755200) = (621156216911:ℝ)/300822783032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2494
  · change lowerPayment 2495 ≤ lowerValue ((point 2 split 4096 2495+point 2 split 4096 2496)/2)
    have hp : lowerPayment 2495 = (276871452803:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2495+point 2 split 4096 2496)/2 = (482903221:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((482903221:ℝ)/168755200)/ClassicalSixthBranch.v ((482903221:ℝ)/168755200) = (621078903237:ℝ)/300774775144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2495
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_155
