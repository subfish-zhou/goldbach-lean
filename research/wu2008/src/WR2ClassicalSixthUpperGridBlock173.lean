import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints173
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_173 (j : Fin 16) : upperPayment (16*173+j.val) ≤
    upperValue ((point split endpoint 4096 (16*173+j.val)+point split endpoint 4096 (16*173+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2768 ≤ upperValue ((point split endpoint 4096 2768+point split endpoint 4096 2769)/2)
    have hp : upperPayment 2768 = (190152380402:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2768+point split endpoint 4096 2769)/2 = (645779327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645779327:ℝ)/168755200)*ClassicalSixthBranch.v ((645779327:ℝ)/168755200)/ClassicalSixthBranch.r = (98695737970577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2768
  · change upperPayment 2769 ≤ upperValue ((point split endpoint 4096 2769+point split endpoint 4096 2770)/2)
    have hp : upperPayment 2769 = (190032001441:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2769+point split endpoint 4096 2770)/2 = (645804477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645804477:ℝ)/168755200)*ClassicalSixthBranch.v ((645804477:ℝ)/168755200)/ClassicalSixthBranch.r = (98675325309081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2769
  · change upperPayment 2770 ≤ upperValue ((point split endpoint 4096 2770+point split endpoint 4096 2771)/2)
    have hp : upperPayment 2770 = (189911591597:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2770+point split endpoint 4096 2771)/2 = (645829627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645829627:ℝ)/168755200)*ClassicalSixthBranch.v ((645829627:ℝ)/168755200)/ClassicalSixthBranch.r = (98654914671657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2770
  · change upperPayment 2771 ≤ upperValue ((point split endpoint 4096 2771+point split endpoint 4096 2772)/2)
    have hp : upperPayment 2771 = (189791150861:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2771+point split endpoint 4096 2772)/2 = (645854777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645854777:ℝ)/168755200)*ClassicalSixthBranch.v ((645854777:ℝ)/168755200)/ClassicalSixthBranch.r = (98634506058305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2771
  · change upperPayment 2772 ≤ upperValue ((point split endpoint 4096 2772+point split endpoint 4096 2773)/2)
    have hp : upperPayment 2772 = (189670679226:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2772+point split endpoint 4096 2773)/2 = (645879927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645879927:ℝ)/168755200)*ClassicalSixthBranch.v ((645879927:ℝ)/168755200)/ClassicalSixthBranch.r = (98614099469025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2772
  · change upperPayment 2773 ≤ upperValue ((point split endpoint 4096 2773+point split endpoint 4096 2774)/2)
    have hp : upperPayment 2773 = (189550176686:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2773+point split endpoint 4096 2774)/2 = (645905077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645905077:ℝ)/168755200)*ClassicalSixthBranch.v ((645905077:ℝ)/168755200)/ClassicalSixthBranch.r = (98593694903817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2773
  · change upperPayment 2774 ≤ upperValue ((point split endpoint 4096 2774+point split endpoint 4096 2775)/2)
    have hp : upperPayment 2774 = (189429643234:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2774+point split endpoint 4096 2775)/2 = (645930227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645930227:ℝ)/168755200)*ClassicalSixthBranch.v ((645930227:ℝ)/168755200)/ClassicalSixthBranch.r = (98573292362681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2774
  · change upperPayment 2775 ≤ upperValue ((point split endpoint 4096 2775+point split endpoint 4096 2776)/2)
    have hp : upperPayment 2775 = (189309078862:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2775+point split endpoint 4096 2776)/2 = (645955377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645955377:ℝ)/168755200)*ClassicalSixthBranch.v ((645955377:ℝ)/168755200)/ClassicalSixthBranch.r = (98552891845617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2775
  · change upperPayment 2776 ≤ upperValue ((point split endpoint 4096 2776+point split endpoint 4096 2777)/2)
    have hp : upperPayment 2776 = (189188483563:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2776+point split endpoint 4096 2777)/2 = (645980527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((645980527:ℝ)/168755200)*ClassicalSixthBranch.v ((645980527:ℝ)/168755200)/ClassicalSixthBranch.r = (98532493352625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2776
  · change upperPayment 2777 ≤ upperValue ((point split endpoint 4096 2777+point split endpoint 4096 2778)/2)
    have hp : upperPayment 2777 = (189067857331:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2777+point split endpoint 4096 2778)/2 = (646005677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646005677:ℝ)/168755200)*ClassicalSixthBranch.v ((646005677:ℝ)/168755200)/ClassicalSixthBranch.r = (98512096883705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2777
  · change upperPayment 2778 ≤ upperValue ((point split endpoint 4096 2778+point split endpoint 4096 2779)/2)
    have hp : upperPayment 2778 = (188947200158:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2778+point split endpoint 4096 2779)/2 = (646030827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646030827:ℝ)/168755200)*ClassicalSixthBranch.v ((646030827:ℝ)/168755200)/ClassicalSixthBranch.r = (98491702438857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2778
  · change upperPayment 2779 ≤ upperValue ((point split endpoint 4096 2779+point split endpoint 4096 2780)/2)
    have hp : upperPayment 2779 = (188826512037:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2779+point split endpoint 4096 2780)/2 = (646055977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646055977:ℝ)/168755200)*ClassicalSixthBranch.v ((646055977:ℝ)/168755200)/ClassicalSixthBranch.r = (98471310018081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2779
  · change upperPayment 2780 ≤ upperValue ((point split endpoint 4096 2780+point split endpoint 4096 2781)/2)
    have hp : upperPayment 2780 = (188705792961:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2780+point split endpoint 4096 2781)/2 = (646081127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646081127:ℝ)/168755200)*ClassicalSixthBranch.v ((646081127:ℝ)/168755200)/ClassicalSixthBranch.r = (98450919621377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2780
  · change upperPayment 2781 ≤ upperValue ((point split endpoint 4096 2781+point split endpoint 4096 2782)/2)
    have hp : upperPayment 2781 = (188585042923:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2781+point split endpoint 4096 2782)/2 = (646106277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646106277:ℝ)/168755200)*ClassicalSixthBranch.v ((646106277:ℝ)/168755200)/ClassicalSixthBranch.r = (98430531248745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2781
  · change upperPayment 2782 ≤ upperValue ((point split endpoint 4096 2782+point split endpoint 4096 2783)/2)
    have hp : upperPayment 2782 = (188464261916:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2782+point split endpoint 4096 2783)/2 = (646131427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646131427:ℝ)/168755200)*ClassicalSixthBranch.v ((646131427:ℝ)/168755200)/ClassicalSixthBranch.r = (98410144900185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2782
  · change upperPayment 2783 ≤ upperValue ((point split endpoint 4096 2783+point split endpoint 4096 2784)/2)
    have hp : upperPayment 2783 = (188343449933:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2783+point split endpoint 4096 2784)/2 = (646156577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646156577:ℝ)/168755200)*ClassicalSixthBranch.v ((646156577:ℝ)/168755200)/ClassicalSixthBranch.r = (98389760575697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2783
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_173
