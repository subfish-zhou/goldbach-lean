import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints037
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_037 (j : Fin 16) : lowerPayment (16*37+j.val) ≤
    lowerValue ((point 2 split 4096 (16*37+j.val)+point 2 split 4096 (16*37+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 592 ≤ lowerValue ((point 2 split 4096 592+point 2 split 4096 593)/2)
    have hp : lowerPayment 592 = (85018269673:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 592+point 2 split 4096 593)/2 = (74406127:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74406127:ℝ)/33751040)/ClassicalSixthBranch.v ((74406127:ℝ)/33751040) = (768206824859:ℝ)/392133786008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_592
  · change lowerPayment 593 ≤ lowerValue ((point 2 split 4096 593+point 2 split 4096 594)/2)
    have hp : lowerPayment 593 = (85145240889:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 593+point 2 split 4096 594)/2 = (372088897:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372088897:ℝ)/168755200)/ClassicalSixthBranch.v ((372088897:ℝ)/168755200) = (153625902237:ℝ)/78417155624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_593
  · change lowerPayment 594 ≤ lowerValue ((point 2 split 4096 594+point 2 split 4096 595)/2)
    have hp : lowerPayment 594 = (85272165809:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 594+point 2 split 4096 595)/2 = (372147159:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372147159:ℝ)/168755200)/ClassicalSixthBranch.v ((372147159:ℝ)/168755200) = (768052197511:ℝ)/392037770232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_594
  · change lowerPayment 595 ≤ lowerValue ((point 2 split 4096 595+point 2 split 4096 596)/2)
    have hp : lowerPayment 595 = (85399044474:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 595+point 2 split 4096 596)/2 = (372205421:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372205421:ℝ)/168755200)/ClassicalSixthBranch.v ((372205421:ℝ)/168755200) = (767974883837:ℝ)/391989762344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_595
  · change lowerPayment 596 ≤ lowerValue ((point 2 split 4096 596+point 2 split 4096 597)/2)
    have hp : lowerPayment 596 = (85525876926:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 596+point 2 split 4096 597)/2 = (372263683:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372263683:ℝ)/168755200)/ClassicalSixthBranch.v ((372263683:ℝ)/168755200) = (767897570163:ℝ)/391941754456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_596
  · change lowerPayment 597 ≤ lowerValue ((point 2 split 4096 597+point 2 split 4096 598)/2)
    have hp : lowerPayment 597 = (85652663204:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 597+point 2 split 4096 598)/2 = (74464389:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74464389:ℝ)/33751040)/ClassicalSixthBranch.v ((74464389:ℝ)/33751040) = (767820256489:ℝ)/391893746568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_597
  · change lowerPayment 598 ≤ lowerValue ((point 2 split 4096 598+point 2 split 4096 599)/2)
    have hp : lowerPayment 598 = (85779403350:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 598+point 2 split 4096 599)/2 = (372380207:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372380207:ℝ)/168755200)/ClassicalSixthBranch.v ((372380207:ℝ)/168755200) = (153548588563:ℝ)/78369147736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_598
  · change lowerPayment 599 ≤ lowerValue ((point 2 split 4096 599+point 2 split 4096 600)/2)
    have hp : lowerPayment 599 = (85906097405:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 599+point 2 split 4096 600)/2 = (372438469:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372438469:ℝ)/168755200)/ClassicalSixthBranch.v ((372438469:ℝ)/168755200) = (767665629141:ℝ)/391797730792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_599
  · change lowerPayment 600 ≤ lowerValue ((point 2 split 4096 600+point 2 split 4096 601)/2)
    have hp : lowerPayment 600 = (86032745410:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 600+point 2 split 4096 601)/2 = (372496731:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372496731:ℝ)/168755200)/ClassicalSixthBranch.v ((372496731:ℝ)/168755200) = (767588315467:ℝ)/391749722904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_600
  · change lowerPayment 601 ≤ lowerValue ((point 2 split 4096 601+point 2 split 4096 602)/2)
    have hp : lowerPayment 601 = (86159347406:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 601+point 2 split 4096 602)/2 = (372554993:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372554993:ℝ)/168755200)/ClassicalSixthBranch.v ((372554993:ℝ)/168755200) = (767511001793:ℝ)/391701715016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_601
  · change lowerPayment 602 ≤ lowerValue ((point 2 split 4096 602+point 2 split 4096 603)/2)
    have hp : lowerPayment 602 = (86285903433:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 602+point 2 split 4096 603)/2 = (74522651:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74522651:ℝ)/33751040)/ClassicalSixthBranch.v ((74522651:ℝ)/33751040) = (767433688119:ℝ)/391653707128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_602
  · change lowerPayment 603 ≤ lowerValue ((point 2 split 4096 603+point 2 split 4096 604)/2)
    have hp : lowerPayment 603 = (86412413533:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 603+point 2 split 4096 604)/2 = (372671517:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372671517:ℝ)/168755200)/ClassicalSixthBranch.v ((372671517:ℝ)/168755200) = (153471274889:ℝ)/78321139848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_603
  · change lowerPayment 604 ≤ lowerValue ((point 2 split 4096 604+point 2 split 4096 605)/2)
    have hp : lowerPayment 604 = (86538877746:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 604+point 2 split 4096 605)/2 = (372729779:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372729779:ℝ)/168755200)/ClassicalSixthBranch.v ((372729779:ℝ)/168755200) = (767279060771:ℝ)/391557691352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_604
  · change lowerPayment 605 ≤ lowerValue ((point 2 split 4096 605+point 2 split 4096 606)/2)
    have hp : lowerPayment 605 = (86665296113:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 605+point 2 split 4096 606)/2 = (372788041:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372788041:ℝ)/168755200)/ClassicalSixthBranch.v ((372788041:ℝ)/168755200) = (767201747097:ℝ)/391509683464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_605
  · change lowerPayment 606 ≤ lowerValue ((point 2 split 4096 606+point 2 split 4096 607)/2)
    have hp : lowerPayment 606 = (86791668674:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 606+point 2 split 4096 607)/2 = (372846303:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((372846303:ℝ)/168755200)/ClassicalSixthBranch.v ((372846303:ℝ)/168755200) = (767124433423:ℝ)/391461675576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_606
  · change lowerPayment 607 ≤ lowerValue ((point 2 split 4096 607+point 2 split 4096 608)/2)
    have hp : lowerPayment 607 = (86917995471:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 607+point 2 split 4096 608)/2 = (74580913:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((74580913:ℝ)/33751040)/ClassicalSixthBranch.v ((74580913:ℝ)/33751040) = (767047119749:ℝ)/391413667688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_607
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_037
