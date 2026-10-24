import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints032
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_032 (j : Fin 16) : upperPayment (16*32+j.val) ≤
    upperValue ((point split endpoint 4096 (16*32+j.val)+point split endpoint 4096 (16*32+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 512 ≤ upperValue ((point split endpoint 4096 512+point split endpoint 4096 513)/2)
    have hp : upperPayment 512 = (394019248366:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 512+point split endpoint 4096 513)/2 = (589040927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589040927:ℝ)/168755200)*ClassicalSixthBranch.v ((589040927:ℝ)/168755200)/ClassicalSixthBranch.r = (149899779114065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_512
  · change upperPayment 513 ≤ upperValue ((point split endpoint 4096 513+point split endpoint 4096 514)/2)
    have hp : upperPayment 513 = (393955006965:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 513+point split endpoint 4096 514)/2 = (589066077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589066077:ℝ)/168755200)*ClassicalSixthBranch.v ((589066077:ℝ)/168755200)/ClassicalSixthBranch.r = (149874800146137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_513
  · change upperPayment 514 ≤ upperValue ((point split endpoint 4096 514+point split endpoint 4096 515)/2)
    have hp : upperPayment 514 = (393890745079:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 514+point split endpoint 4096 515)/2 = (589091227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589091227:ℝ)/168755200)*ClassicalSixthBranch.v ((589091227:ℝ)/168755200)/ClassicalSixthBranch.r = (149849823202281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_514
  · change upperPayment 515 ≤ upperValue ((point split endpoint 4096 515+point split endpoint 4096 516)/2)
    have hp : upperPayment 515 = (393826462706:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 515+point split endpoint 4096 516)/2 = (589116377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589116377:ℝ)/168755200)*ClassicalSixthBranch.v ((589116377:ℝ)/168755200)/ClassicalSixthBranch.r = (149824848282497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_515
  · change upperPayment 516 ≤ upperValue ((point split endpoint 4096 516+point split endpoint 4096 517)/2)
    have hp : upperPayment 516 = (393762159844:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 516+point split endpoint 4096 517)/2 = (589141527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589141527:ℝ)/168755200)*ClassicalSixthBranch.v ((589141527:ℝ)/168755200)/ClassicalSixthBranch.r = (149799875386785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_516
  · change upperPayment 517 ≤ upperValue ((point split endpoint 4096 517+point split endpoint 4096 518)/2)
    have hp : upperPayment 517 = (393697836489:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 517+point split endpoint 4096 518)/2 = (589166677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589166677:ℝ)/168755200)*ClassicalSixthBranch.v ((589166677:ℝ)/168755200)/ClassicalSixthBranch.r = (149774904515145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_517
  · change upperPayment 518 ≤ upperValue ((point split endpoint 4096 518+point split endpoint 4096 519)/2)
    have hp : upperPayment 518 = (393633492639:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 518+point split endpoint 4096 519)/2 = (5720309:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5720309:ℝ)/1638400)*ClassicalSixthBranch.v ((5720309:ℝ)/1638400)/ClassicalSixthBranch.r = (1453882870559:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_518
  · change upperPayment 519 ≤ upperValue ((point split endpoint 4096 519+point split endpoint 4096 520)/2)
    have hp : upperPayment 519 = (393569128291:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 519+point split endpoint 4096 520)/2 = (589216977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589216977:ℝ)/168755200)*ClassicalSixthBranch.v ((589216977:ℝ)/168755200)/ClassicalSixthBranch.r = (149724968844081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_519
  · change upperPayment 520 ≤ upperValue ((point split endpoint 4096 520+point split endpoint 4096 521)/2)
    have hp : upperPayment 520 = (393504743442:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 520+point split endpoint 4096 521)/2 = (589242127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589242127:ℝ)/168755200)*ClassicalSixthBranch.v ((589242127:ℝ)/168755200)/ClassicalSixthBranch.r = (149700004044657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_520
  · change upperPayment 521 ≤ upperValue ((point split endpoint 4096 521+point split endpoint 4096 522)/2)
    have hp : upperPayment 521 = (393440338090:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 521+point split endpoint 4096 522)/2 = (589267277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589267277:ℝ)/168755200)*ClassicalSixthBranch.v ((589267277:ℝ)/168755200)/ClassicalSixthBranch.r = (149675041269305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_521
  · change upperPayment 522 ≤ upperValue ((point split endpoint 4096 522+point split endpoint 4096 523)/2)
    have hp : upperPayment 522 = (393375912232:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 522+point split endpoint 4096 523)/2 = (589292427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589292427:ℝ)/168755200)*ClassicalSixthBranch.v ((589292427:ℝ)/168755200)/ClassicalSixthBranch.r = (149650080518025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_522
  · change upperPayment 523 ≤ upperValue ((point split endpoint 4096 523+point split endpoint 4096 524)/2)
    have hp : upperPayment 523 = (393311465864:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 523+point split endpoint 4096 524)/2 = (589317577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589317577:ℝ)/168755200)*ClassicalSixthBranch.v ((589317577:ℝ)/168755200)/ClassicalSixthBranch.r = (149625121790817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_523
  · change upperPayment 524 ≤ upperValue ((point split endpoint 4096 524+point split endpoint 4096 525)/2)
    have hp : upperPayment 524 = (393246998986:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 524+point split endpoint 4096 525)/2 = (589342727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589342727:ℝ)/168755200)*ClassicalSixthBranch.v ((589342727:ℝ)/168755200)/ClassicalSixthBranch.r = (149600165087681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_524
  · change upperPayment 525 ≤ upperValue ((point split endpoint 4096 525+point split endpoint 4096 526)/2)
    have hp : upperPayment 525 = (393182511592:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 525+point split endpoint 4096 526)/2 = (589367877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589367877:ℝ)/168755200)*ClassicalSixthBranch.v ((589367877:ℝ)/168755200)/ClassicalSixthBranch.r = (149575210408617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_525
  · change upperPayment 526 ≤ upperValue ((point split endpoint 4096 526+point split endpoint 4096 527)/2)
    have hp : upperPayment 526 = (393118003682:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 526+point split endpoint 4096 527)/2 = (589393027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589393027:ℝ)/168755200)*ClassicalSixthBranch.v ((589393027:ℝ)/168755200)/ClassicalSixthBranch.r = (149550257753625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_526
  · change upperPayment 527 ≤ upperValue ((point split endpoint 4096 527+point split endpoint 4096 528)/2)
    have hp : upperPayment 527 = (393053475252:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 527+point split endpoint 4096 528)/2 = (589418177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((589418177:ℝ)/168755200)*ClassicalSixthBranch.v ((589418177:ℝ)/168755200)/ClassicalSixthBranch.r = (149525307122705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_527
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_032
