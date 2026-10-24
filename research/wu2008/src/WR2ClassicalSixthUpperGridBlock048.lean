import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints048
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_048 (j : Fin 16) : upperPayment (16*48+j.val) ≤
    upperValue ((point split endpoint 4096 (16*48+j.val)+point split endpoint 4096 (16*48+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 768 ≤ upperValue ((point split endpoint 4096 768+point split endpoint 4096 769)/2)
    have hp : upperPayment 768 = (376897058344:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 768+point split endpoint 4096 769)/2 = (595479327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595479327:ℝ)/168755200)*ClassicalSixthBranch.v ((595479327:ℝ)/168755200)/ClassicalSixthBranch.r = (143571229034577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_768
  · change upperPayment 769 ≤ upperValue ((point split endpoint 4096 769+point split endpoint 4096 770)/2)
    have hp : upperPayment 769 = (376827480087:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 769+point split endpoint 4096 770)/2 = (595504477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595504477:ℝ)/168755200)*ClassicalSixthBranch.v ((595504477:ℝ)/168755200)/ClassicalSixthBranch.r = (143546768229081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_769
  · change upperPayment 770 ≤ upperValue ((point split endpoint 4096 770+point split endpoint 4096 771)/2)
    have hp : upperPayment 770 = (376757880603:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 770+point split endpoint 4096 771)/2 = (595529627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595529627:ℝ)/168755200)*ClassicalSixthBranch.v ((595529627:ℝ)/168755200)/ClassicalSixthBranch.r = (143522309447657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_770
  · change upperPayment 771 ≤ upperValue ((point split endpoint 4096 771+point split endpoint 4096 772)/2)
    have hp : upperPayment 771 = (376688259888:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 771+point split endpoint 4096 772)/2 = (595554777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595554777:ℝ)/168755200)*ClassicalSixthBranch.v ((595554777:ℝ)/168755200)/ClassicalSixthBranch.r = (143497852690305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_771
  · change upperPayment 772 ≤ upperValue ((point split endpoint 4096 772+point split endpoint 4096 773)/2)
    have hp : upperPayment 772 = (376618617939:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 772+point split endpoint 4096 773)/2 = (595579927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595579927:ℝ)/168755200)*ClassicalSixthBranch.v ((595579927:ℝ)/168755200)/ClassicalSixthBranch.r = (143473397957025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_772
  · change upperPayment 773 ≤ upperValue ((point split endpoint 4096 773+point split endpoint 4096 774)/2)
    have hp : upperPayment 773 = (376548954753:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 773+point split endpoint 4096 774)/2 = (595605077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595605077:ℝ)/168755200)*ClassicalSixthBranch.v ((595605077:ℝ)/168755200)/ClassicalSixthBranch.r = (143448945247817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_773
  · change upperPayment 774 ≤ upperValue ((point split endpoint 4096 774+point split endpoint 4096 775)/2)
    have hp : upperPayment 774 = (376479270328:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 774+point split endpoint 4096 775)/2 = (595630227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595630227:ℝ)/168755200)*ClassicalSixthBranch.v ((595630227:ℝ)/168755200)/ClassicalSixthBranch.r = (143424494562681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_774
  · change upperPayment 775 ≤ upperValue ((point split endpoint 4096 775+point split endpoint 4096 776)/2)
    have hp : upperPayment 775 = (376409564660:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 775+point split endpoint 4096 776)/2 = (595655377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595655377:ℝ)/168755200)*ClassicalSixthBranch.v ((595655377:ℝ)/168755200)/ClassicalSixthBranch.r = (143400045901617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_775
  · change upperPayment 776 ≤ upperValue ((point split endpoint 4096 776+point split endpoint 4096 777)/2)
    have hp : upperPayment 776 = (376339837745:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 776+point split endpoint 4096 777)/2 = (595680527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595680527:ℝ)/168755200)*ClassicalSixthBranch.v ((595680527:ℝ)/168755200)/ClassicalSixthBranch.r = (143375599264625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_776
  · change upperPayment 777 ≤ upperValue ((point split endpoint 4096 777+point split endpoint 4096 778)/2)
    have hp : upperPayment 777 = (376270089582:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 777+point split endpoint 4096 778)/2 = (595705677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595705677:ℝ)/168755200)*ClassicalSixthBranch.v ((595705677:ℝ)/168755200)/ClassicalSixthBranch.r = (143351154651705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_777
  · change upperPayment 778 ≤ upperValue ((point split endpoint 4096 778+point split endpoint 4096 779)/2)
    have hp : upperPayment 778 = (376200320166:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 778+point split endpoint 4096 779)/2 = (595730827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595730827:ℝ)/168755200)*ClassicalSixthBranch.v ((595730827:ℝ)/168755200)/ClassicalSixthBranch.r = (108008072391:ℝ)/55297703936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_778
  · change upperPayment 779 ≤ upperValue ((point split endpoint 4096 779+point split endpoint 4096 780)/2)
    have hp : upperPayment 779 = (376130529495:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 779+point split endpoint 4096 780)/2 = (595755977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595755977:ℝ)/168755200)*ClassicalSixthBranch.v ((595755977:ℝ)/168755200)/ClassicalSixthBranch.r = (143302271498081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_779
  · change upperPayment 780 ≤ upperValue ((point split endpoint 4096 780+point split endpoint 4096 781)/2)
    have hp : upperPayment 780 = (376060717566:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 780+point split endpoint 4096 781)/2 = (595781127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595781127:ℝ)/168755200)*ClassicalSixthBranch.v ((595781127:ℝ)/168755200)/ClassicalSixthBranch.r = (143277832957377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_780
  · change upperPayment 781 ≤ upperValue ((point split endpoint 4096 781+point split endpoint 4096 782)/2)
    have hp : upperPayment 781 = (375990884375:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 781+point split endpoint 4096 782)/2 = (595806277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595806277:ℝ)/168755200)*ClassicalSixthBranch.v ((595806277:ℝ)/168755200)/ClassicalSixthBranch.r = (143253396440745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_781
  · change upperPayment 782 ≤ upperValue ((point split endpoint 4096 782+point split endpoint 4096 783)/2)
    have hp : upperPayment 782 = (375921029919:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 782+point split endpoint 4096 783)/2 = (595831427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595831427:ℝ)/168755200)*ClassicalSixthBranch.v ((595831427:ℝ)/168755200)/ClassicalSixthBranch.r = (143228961948185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_782
  · change upperPayment 783 ≤ upperValue ((point split endpoint 4096 783+point split endpoint 4096 784)/2)
    have hp : upperPayment 783 = (375851154196:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 783+point split endpoint 4096 784)/2 = (595856577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595856577:ℝ)/168755200)*ClassicalSixthBranch.v ((595856577:ℝ)/168755200)/ClassicalSixthBranch.r = (143204529479697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_783
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_048
