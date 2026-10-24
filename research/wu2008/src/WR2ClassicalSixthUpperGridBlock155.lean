import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints155
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_155 (j : Fin 16) : upperPayment (16*155+j.val) ≤
    upperValue ((point split endpoint 4096 (16*155+j.val)+point split endpoint 4096 (16*155+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2480 ≤ upperValue ((point split endpoint 4096 2480+point split endpoint 4096 2481)/2)
    have hp : upperPayment 2480 = (223563794636:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2480+point split endpoint 4096 2481)/2 = (638536127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638536127:ℝ)/168755200)*ClassicalSixthBranch.v ((638536127:ℝ)/168755200)/ClassicalSixthBranch.r = (104658818261777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2480
  · change upperPayment 2481 ≤ upperValue ((point split endpoint 4096 2481+point split endpoint 4096 2482)/2)
    have hp : upperPayment 2481 = (223452028002:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2481+point split endpoint 4096 2482)/2 = (638561277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638561277:ℝ)/168755200)*ClassicalSixthBranch.v ((638561277:ℝ)/168755200)/ClassicalSixthBranch.r = (104637822667545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2481
  · change upperPayment 2482 ≤ upperValue ((point split endpoint 4096 2482+point split endpoint 4096 2483)/2)
    have hp : upperPayment 2482 = (223340232400:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2482+point split endpoint 4096 2483)/2 = (638586427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638586427:ℝ)/168755200)*ClassicalSixthBranch.v ((638586427:ℝ)/168755200)/ClassicalSixthBranch.r = (104616829097385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2482
  · change upperPayment 2483 ≤ upperValue ((point split endpoint 4096 2483+point split endpoint 4096 2484)/2)
    have hp : upperPayment 2483 = (223228407826:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2483+point split endpoint 4096 2484)/2 = (638611577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638611577:ℝ)/168755200)*ClassicalSixthBranch.v ((638611577:ℝ)/168755200)/ClassicalSixthBranch.r = (104595837551297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2483
  · change upperPayment 2484 ≤ upperValue ((point split endpoint 4096 2484+point split endpoint 4096 2485)/2)
    have hp : upperPayment 2484 = (223116554271:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2484+point split endpoint 4096 2485)/2 = (638636727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638636727:ℝ)/168755200)*ClassicalSixthBranch.v ((638636727:ℝ)/168755200)/ClassicalSixthBranch.r = (104574848029281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2484
  · change upperPayment 2485 ≤ upperValue ((point split endpoint 4096 2485+point split endpoint 4096 2486)/2)
    have hp : upperPayment 2485 = (223004671730:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2485+point split endpoint 4096 2486)/2 = (638661877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638661877:ℝ)/168755200)*ClassicalSixthBranch.v ((638661877:ℝ)/168755200)/ClassicalSixthBranch.r = (104553860531337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2485
  · change upperPayment 2486 ≤ upperValue ((point split endpoint 4096 2486+point split endpoint 4096 2487)/2)
    have hp : upperPayment 2486 = (222892760197:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2486+point split endpoint 4096 2487)/2 = (638687027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638687027:ℝ)/168755200)*ClassicalSixthBranch.v ((638687027:ℝ)/168755200)/ClassicalSixthBranch.r = (104532875057465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2486
  · change upperPayment 2487 ≤ upperValue ((point split endpoint 4096 2487+point split endpoint 4096 2488)/2)
    have hp : upperPayment 2487 = (222780819666:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2487+point split endpoint 4096 2488)/2 = (638712177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638712177:ℝ)/168755200)*ClassicalSixthBranch.v ((638712177:ℝ)/168755200)/ClassicalSixthBranch.r = (104511891607665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2487
  · change upperPayment 2488 ≤ upperValue ((point split endpoint 4096 2488+point split endpoint 4096 2489)/2)
    have hp : upperPayment 2488 = (222668850129:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2488+point split endpoint 4096 2489)/2 = (638737327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638737327:ℝ)/168755200)*ClassicalSixthBranch.v ((638737327:ℝ)/168755200)/ClassicalSixthBranch.r = (104490910181937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2488
  · change upperPayment 2489 ≤ upperValue ((point split endpoint 4096 2489+point split endpoint 4096 2490)/2)
    have hp : upperPayment 2489 = (222556851581:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2489+point split endpoint 4096 2490)/2 = (638762477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638762477:ℝ)/168755200)*ClassicalSixthBranch.v ((638762477:ℝ)/168755200)/ClassicalSixthBranch.r = (104469930780281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2489
  · change upperPayment 2490 ≤ upperValue ((point split endpoint 4096 2490+point split endpoint 4096 2491)/2)
    have hp : upperPayment 2490 = (222444824016:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2490+point split endpoint 4096 2491)/2 = (638787627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638787627:ℝ)/168755200)*ClassicalSixthBranch.v ((638787627:ℝ)/168755200)/ClassicalSixthBranch.r = (104448953402697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2490
  · change upperPayment 2491 ≤ upperValue ((point split endpoint 4096 2491+point split endpoint 4096 2492)/2)
    have hp : upperPayment 2491 = (222332767427:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2491+point split endpoint 4096 2492)/2 = (638812777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638812777:ℝ)/168755200)*ClassicalSixthBranch.v ((638812777:ℝ)/168755200)/ClassicalSixthBranch.r = (104427978049185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2491
  · change upperPayment 2492 ≤ upperValue ((point split endpoint 4096 2492+point split endpoint 4096 2493)/2)
    have hp : upperPayment 2492 = (222220681808:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2492+point split endpoint 4096 2493)/2 = (638837927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638837927:ℝ)/168755200)*ClassicalSixthBranch.v ((638837927:ℝ)/168755200)/ClassicalSixthBranch.r = (104407004719745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2492
  · change upperPayment 2493 ≤ upperValue ((point split endpoint 4096 2493+point split endpoint 4096 2494)/2)
    have hp : upperPayment 2493 = (222108567153:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2493+point split endpoint 4096 2494)/2 = (638863077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638863077:ℝ)/168755200)*ClassicalSixthBranch.v ((638863077:ℝ)/168755200)/ClassicalSixthBranch.r = (104386033414377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2493
  · change upperPayment 2494 ≤ upperValue ((point split endpoint 4096 2494+point split endpoint 4096 2495)/2)
    have hp : upperPayment 2494 = (221996423455:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2494+point split endpoint 4096 2495)/2 = (638888227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638888227:ℝ)/168755200)*ClassicalSixthBranch.v ((638888227:ℝ)/168755200)/ClassicalSixthBranch.r = (104365064133081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2494
  · change upperPayment 2495 ≤ upperValue ((point split endpoint 4096 2495+point split endpoint 4096 2496)/2)
    have hp : upperPayment 2495 = (221884250708:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2495+point split endpoint 4096 2496)/2 = (638913377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638913377:ℝ)/168755200)*ClassicalSixthBranch.v ((638913377:ℝ)/168755200)/ClassicalSixthBranch.r = (104344096875857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2495
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_155
