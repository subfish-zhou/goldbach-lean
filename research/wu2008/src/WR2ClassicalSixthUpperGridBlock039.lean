import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints039
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_039 (j : Fin 16) : upperPayment (16*39+j.val) ≤
    upperValue ((point split endpoint 4096 (16*39+j.val)+point split endpoint 4096 (16*39+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 624 ≤ upperValue ((point split endpoint 4096 624+point split endpoint 4096 625)/2)
    have hp : upperPayment 624 = (386696250071:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 624+point split endpoint 4096 625)/2 = (591857727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591857727:ℝ)/168755200)*ClassicalSixthBranch.v ((591857727:ℝ)/168755200)/ClassicalSixthBranch.r = (147114716337681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_624
  · change upperPayment 625 ≤ upperValue ((point split endpoint 4096 625+point split endpoint 4096 626)/2)
    have hp : upperPayment 625 = (386629697142:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 625+point split endpoint 4096 626)/2 = (591882877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591882877:ℝ)/168755200)*ClassicalSixthBranch.v ((591882877:ℝ)/168755200)/ClassicalSixthBranch.r = (147089964065817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_625
  · change upperPayment 626 ≤ upperValue ((point split endpoint 4096 626+point split endpoint 4096 627)/2)
    have hp : upperPayment 626 = (386563123414:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 626+point split endpoint 4096 627)/2 = (591908027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591908027:ℝ)/168755200)*ClassicalSixthBranch.v ((591908027:ℝ)/168755200)/ClassicalSixthBranch.r = (147065213818025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_626
  · change upperPayment 627 ≤ upperValue ((point split endpoint 4096 627+point split endpoint 4096 628)/2)
    have hp : upperPayment 627 = (386496528885:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 627+point split endpoint 4096 628)/2 = (591933177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591933177:ℝ)/168755200)*ClassicalSixthBranch.v ((591933177:ℝ)/168755200)/ClassicalSixthBranch.r = (147040465594305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_627
  · change upperPayment 628 ≤ upperValue ((point split endpoint 4096 628+point split endpoint 4096 629)/2)
    have hp : upperPayment 628 = (386429913551:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 628+point split endpoint 4096 629)/2 = (591958327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591958327:ℝ)/168755200)*ClassicalSixthBranch.v ((591958327:ℝ)/168755200)/ClassicalSixthBranch.r = (147015719394657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_628
  · change upperPayment 629 ≤ upperValue ((point split endpoint 4096 629+point split endpoint 4096 630)/2)
    have hp : upperPayment 629 = (386363277410:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 629+point split endpoint 4096 630)/2 = (591983477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((591983477:ℝ)/168755200)*ClassicalSixthBranch.v ((591983477:ℝ)/168755200)/ClassicalSixthBranch.r = (146990975219081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_629
  · change upperPayment 630 ≤ upperValue ((point split endpoint 4096 630+point split endpoint 4096 631)/2)
    have hp : upperPayment 630 = (386296620459:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 630+point split endpoint 4096 631)/2 = (592008627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592008627:ℝ)/168755200)*ClassicalSixthBranch.v ((592008627:ℝ)/168755200)/ClassicalSixthBranch.r = (146966233067577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_630
  · change upperPayment 631 ≤ upperValue ((point split endpoint 4096 631+point split endpoint 4096 632)/2)
    have hp : upperPayment 631 = (386229942695:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 631+point split endpoint 4096 632)/2 = (592033777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592033777:ℝ)/168755200)*ClassicalSixthBranch.v ((592033777:ℝ)/168755200)/ClassicalSixthBranch.r = (146941492940145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_631
  · change upperPayment 632 ≤ upperValue ((point split endpoint 4096 632+point split endpoint 4096 633)/2)
    have hp : upperPayment 632 = (386163244114:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 632+point split endpoint 4096 633)/2 = (592058927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592058927:ℝ)/168755200)*ClassicalSixthBranch.v ((592058927:ℝ)/168755200)/ClassicalSixthBranch.r = (146916754836785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_632
  · change upperPayment 633 ≤ upperValue ((point split endpoint 4096 633+point split endpoint 4096 634)/2)
    have hp : upperPayment 633 = (386096524716:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 633+point split endpoint 4096 634)/2 = (592084077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592084077:ℝ)/168755200)*ClassicalSixthBranch.v ((592084077:ℝ)/168755200)/ClassicalSixthBranch.r = (146892018757497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_633
  · change upperPayment 634 ≤ upperValue ((point split endpoint 4096 634+point split endpoint 4096 635)/2)
    have hp : upperPayment 634 = (386029784495:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 634+point split endpoint 4096 635)/2 = (592109227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592109227:ℝ)/168755200)*ClassicalSixthBranch.v ((592109227:ℝ)/168755200)/ClassicalSixthBranch.r = (146867284702281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_634
  · change upperPayment 635 ≤ upperValue ((point split endpoint 4096 635+point split endpoint 4096 636)/2)
    have hp : upperPayment 635 = (385963023450:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 635+point split endpoint 4096 636)/2 = (592134377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592134377:ℝ)/168755200)*ClassicalSixthBranch.v ((592134377:ℝ)/168755200)/ClassicalSixthBranch.r = (146842552671137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_635
  · change upperPayment 636 ≤ upperValue ((point split endpoint 4096 636+point split endpoint 4096 637)/2)
    have hp : upperPayment 636 = (385896241577:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 636+point split endpoint 4096 637)/2 = (592159527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592159527:ℝ)/168755200)*ClassicalSixthBranch.v ((592159527:ℝ)/168755200)/ClassicalSixthBranch.r = (146817822664065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_636
  · change upperPayment 637 ≤ upperValue ((point split endpoint 4096 637+point split endpoint 4096 638)/2)
    have hp : upperPayment 637 = (385829438874:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 637+point split endpoint 4096 638)/2 = (592184677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592184677:ℝ)/168755200)*ClassicalSixthBranch.v ((592184677:ℝ)/168755200)/ClassicalSixthBranch.r = (146793094681065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_637
  · change upperPayment 638 ≤ upperValue ((point split endpoint 4096 638+point split endpoint 4096 639)/2)
    have hp : upperPayment 638 = (385762615338:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 638+point split endpoint 4096 639)/2 = (592209827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592209827:ℝ)/168755200)*ClassicalSixthBranch.v ((592209827:ℝ)/168755200)/ClassicalSixthBranch.r = (146768368722137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_638
  · change upperPayment 639 ≤ upperValue ((point split endpoint 4096 639+point split endpoint 4096 640)/2)
    have hp : upperPayment 639 = (385695770966:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 639+point split endpoint 4096 640)/2 = (592234977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((592234977:ℝ)/168755200)*ClassicalSixthBranch.v ((592234977:ℝ)/168755200)/ClassicalSixthBranch.r = (146743644787281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_639
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_039
