import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints030
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_030 (j : Fin 16) : upperPayment (16*30+j.val) ≤
    upperValue ((point split endpoint 4096 (16*30+j.val)+point split endpoint 4096 (16*30+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 480 ≤ upperValue ((point split endpoint 4096 480+point split endpoint 4096 481)/2)
    have hp : upperPayment 480 = (396064173807:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 480+point split endpoint 4096 481)/2 = (588236127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588236127:ℝ)/168755200)*ClassicalSixthBranch.v ((588236127:ℝ)/168755200)/ClassicalSixthBranch.r = (150700174797777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_480
  · change upperPayment 481 ≤ upperValue ((point split endpoint 4096 481+point split endpoint 4096 482)/2)
    have hp : upperPayment 481 = (396000586467:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 481+point split endpoint 4096 482)/2 = (588261277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588261277:ℝ)/168755200)*ClassicalSixthBranch.v ((588261277:ℝ)/168755200)/ClassicalSixthBranch.r = (150675131059545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_481
  · change upperPayment 482 ≤ upperValue ((point split endpoint 4096 482+point split endpoint 4096 483)/2)
    have hp : upperPayment 482 = (395936978729:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 482+point split endpoint 4096 483)/2 = (588286427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588286427:ℝ)/168755200)*ClassicalSixthBranch.v ((588286427:ℝ)/168755200)/ClassicalSixthBranch.r = (150650089345385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_482
  · change upperPayment 483 ≤ upperValue ((point split endpoint 4096 483+point split endpoint 4096 484)/2)
    have hp : upperPayment 483 = (395873350591:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 483+point split endpoint 4096 484)/2 = (588311577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588311577:ℝ)/168755200)*ClassicalSixthBranch.v ((588311577:ℝ)/168755200)/ClassicalSixthBranch.r = (150625049655297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_483
  · change upperPayment 484 ≤ upperValue ((point split endpoint 4096 484+point split endpoint 4096 485)/2)
    have hp : upperPayment 484 = (395809702050:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 484+point split endpoint 4096 485)/2 = (588336727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588336727:ℝ)/168755200)*ClassicalSixthBranch.v ((588336727:ℝ)/168755200)/ClassicalSixthBranch.r = (150600011989281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_484
  · change upperPayment 485 ≤ upperValue ((point split endpoint 4096 485+point split endpoint 4096 486)/2)
    have hp : upperPayment 485 = (395746033104:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 485+point split endpoint 4096 486)/2 = (588361877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588361877:ℝ)/168755200)*ClassicalSixthBranch.v ((588361877:ℝ)/168755200)/ClassicalSixthBranch.r = (150574976347337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_485
  · change upperPayment 486 ≤ upperValue ((point split endpoint 4096 486+point split endpoint 4096 487)/2)
    have hp : upperPayment 486 = (395682343749:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 486+point split endpoint 4096 487)/2 = (588387027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588387027:ℝ)/168755200)*ClassicalSixthBranch.v ((588387027:ℝ)/168755200)/ClassicalSixthBranch.r = (150549942729465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_486
  · change upperPayment 487 ≤ upperValue ((point split endpoint 4096 487+point split endpoint 4096 488)/2)
    have hp : upperPayment 487 = (395618633983:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 487+point split endpoint 4096 488)/2 = (588412177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588412177:ℝ)/168755200)*ClassicalSixthBranch.v ((588412177:ℝ)/168755200)/ClassicalSixthBranch.r = (150524911135665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_487
  · change upperPayment 488 ≤ upperValue ((point split endpoint 4096 488+point split endpoint 4096 489)/2)
    have hp : upperPayment 488 = (395554903804:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 488+point split endpoint 4096 489)/2 = (588437327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588437327:ℝ)/168755200)*ClassicalSixthBranch.v ((588437327:ℝ)/168755200)/ClassicalSixthBranch.r = (150499881565937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_488
  · change upperPayment 489 ≤ upperValue ((point split endpoint 4096 489+point split endpoint 4096 490)/2)
    have hp : upperPayment 489 = (395491153208:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 489+point split endpoint 4096 490)/2 = (588462477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588462477:ℝ)/168755200)*ClassicalSixthBranch.v ((588462477:ℝ)/168755200)/ClassicalSixthBranch.r = (150474854020281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_489
  · change upperPayment 490 ≤ upperValue ((point split endpoint 4096 490+point split endpoint 4096 491)/2)
    have hp : upperPayment 490 = (395427382194:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 490+point split endpoint 4096 491)/2 = (588487627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588487627:ℝ)/168755200)*ClassicalSixthBranch.v ((588487627:ℝ)/168755200)/ClassicalSixthBranch.r = (150449828498697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_490
  · change upperPayment 491 ≤ upperValue ((point split endpoint 4096 491+point split endpoint 4096 492)/2)
    have hp : upperPayment 491 = (395363590757:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 491+point split endpoint 4096 492)/2 = (588512777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588512777:ℝ)/168755200)*ClassicalSixthBranch.v ((588512777:ℝ)/168755200)/ClassicalSixthBranch.r = (150424805001185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_491
  · change upperPayment 492 ≤ upperValue ((point split endpoint 4096 492+point split endpoint 4096 493)/2)
    have hp : upperPayment 492 = (395299778896:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 492+point split endpoint 4096 493)/2 = (588537927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588537927:ℝ)/168755200)*ClassicalSixthBranch.v ((588537927:ℝ)/168755200)/ClassicalSixthBranch.r = (150399783527745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_492
  · change upperPayment 493 ≤ upperValue ((point split endpoint 4096 493+point split endpoint 4096 494)/2)
    have hp : upperPayment 493 = (395235946608:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 493+point split endpoint 4096 494)/2 = (588563077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588563077:ℝ)/168755200)*ClassicalSixthBranch.v ((588563077:ℝ)/168755200)/ClassicalSixthBranch.r = (150374764078377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_493
  · change upperPayment 494 ≤ upperValue ((point split endpoint 4096 494+point split endpoint 4096 495)/2)
    have hp : upperPayment 494 = (395172093890:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 494+point split endpoint 4096 495)/2 = (588588227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588588227:ℝ)/168755200)*ClassicalSixthBranch.v ((588588227:ℝ)/168755200)/ClassicalSixthBranch.r = (150349746653081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_494
  · change upperPayment 495 ≤ upperValue ((point split endpoint 4096 495+point split endpoint 4096 496)/2)
    have hp : upperPayment 495 = (395108220740:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 495+point split endpoint 4096 496)/2 = (588613377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((588613377:ℝ)/168755200)*ClassicalSixthBranch.v ((588613377:ℝ)/168755200)/ClassicalSixthBranch.r = (150324731251857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_495
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_030
