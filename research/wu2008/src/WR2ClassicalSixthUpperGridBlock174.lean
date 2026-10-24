import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints174
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_174 (j : Fin 16) : upperPayment (16*174+j.val) ≤
    upperValue ((point split endpoint 4096 (16*174+j.val)+point split endpoint 4096 (16*174+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2784 ≤ upperValue ((point split endpoint 4096 2784+point split endpoint 4096 2785)/2)
    have hp : upperPayment 2784 = (188222606967:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2784+point split endpoint 4096 2785)/2 = (6273609:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6273609:ℝ)/1638400)*ClassicalSixthBranch.v ((6273609:ℝ)/1638400)/ClassicalSixthBranch.r = (955042507527:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2784
  · change upperPayment 2785 ≤ upperValue ((point split endpoint 4096 2785+point split endpoint 4096 2786)/2)
    have hp : upperPayment 2785 = (188101733010:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2785+point split endpoint 4096 2786)/2 = (646206877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646206877:ℝ)/168755200)*ClassicalSixthBranch.v ((646206877:ℝ)/168755200)/ClassicalSixthBranch.r = (98348997998937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2785
  · change upperPayment 2786 ≤ upperValue ((point split endpoint 4096 2786+point split endpoint 4096 2787)/2)
    have hp : upperPayment 2786 = (187980828056:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2786+point split endpoint 4096 2787)/2 = (646232027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646232027:ℝ)/168755200)*ClassicalSixthBranch.v ((646232027:ℝ)/168755200)/ClassicalSixthBranch.r = (98328619746665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2786
  · change upperPayment 2787 ≤ upperValue ((point split endpoint 4096 2787+point split endpoint 4096 2788)/2)
    have hp : upperPayment 2787 = (187859892097:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2787+point split endpoint 4096 2788)/2 = (646257177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646257177:ℝ)/168755200)*ClassicalSixthBranch.v ((646257177:ℝ)/168755200)/ClassicalSixthBranch.r = (98308243518465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2787
  · change upperPayment 2788 ≤ upperValue ((point split endpoint 4096 2788+point split endpoint 4096 2789)/2)
    have hp : upperPayment 2788 = (187738925126:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2788+point split endpoint 4096 2789)/2 = (646282327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646282327:ℝ)/168755200)*ClassicalSixthBranch.v ((646282327:ℝ)/168755200)/ClassicalSixthBranch.r = (98287869314337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2788
  · change upperPayment 2789 ≤ upperValue ((point split endpoint 4096 2789+point split endpoint 4096 2790)/2)
    have hp : upperPayment 2789 = (187617927137:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2789+point split endpoint 4096 2790)/2 = (646307477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646307477:ℝ)/168755200)*ClassicalSixthBranch.v ((646307477:ℝ)/168755200)/ClassicalSixthBranch.r = (98267497134281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2789
  · change upperPayment 2790 ≤ upperValue ((point split endpoint 4096 2790+point split endpoint 4096 2791)/2)
    have hp : upperPayment 2790 = (187496898122:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2790+point split endpoint 4096 2791)/2 = (646332627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646332627:ℝ)/168755200)*ClassicalSixthBranch.v ((646332627:ℝ)/168755200)/ClassicalSixthBranch.r = (98247126978297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2790
  · change upperPayment 2791 ≤ upperValue ((point split endpoint 4096 2791+point split endpoint 4096 2792)/2)
    have hp : upperPayment 2791 = (187375838074:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2791+point split endpoint 4096 2792)/2 = (646357777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646357777:ℝ)/168755200)*ClassicalSixthBranch.v ((646357777:ℝ)/168755200)/ClassicalSixthBranch.r = (98226758846385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2791
  · change upperPayment 2792 ≤ upperValue ((point split endpoint 4096 2792+point split endpoint 4096 2793)/2)
    have hp : upperPayment 2792 = (187254746986:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2792+point split endpoint 4096 2793)/2 = (646382927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646382927:ℝ)/168755200)*ClassicalSixthBranch.v ((646382927:ℝ)/168755200)/ClassicalSixthBranch.r = (98206392738545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2792
  · change upperPayment 2793 ≤ upperValue ((point split endpoint 4096 2793+point split endpoint 4096 2794)/2)
    have hp : upperPayment 2793 = (187133624851:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2793+point split endpoint 4096 2794)/2 = (646408077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646408077:ℝ)/168755200)*ClassicalSixthBranch.v ((646408077:ℝ)/168755200)/ClassicalSixthBranch.r = (98186028654777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2793
  · change upperPayment 2794 ≤ upperValue ((point split endpoint 4096 2794+point split endpoint 4096 2795)/2)
    have hp : upperPayment 2794 = (187012471661:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2794+point split endpoint 4096 2795)/2 = (646433227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646433227:ℝ)/168755200)*ClassicalSixthBranch.v ((646433227:ℝ)/168755200)/ClassicalSixthBranch.r = (98165666595081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2794
  · change upperPayment 2795 ≤ upperValue ((point split endpoint 4096 2795+point split endpoint 4096 2796)/2)
    have hp : upperPayment 2795 = (186891287410:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2795+point split endpoint 4096 2796)/2 = (646458377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646458377:ℝ)/168755200)*ClassicalSixthBranch.v ((646458377:ℝ)/168755200)/ClassicalSixthBranch.r = (98145306559457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2795
  · change upperPayment 2796 ≤ upperValue ((point split endpoint 4096 2796+point split endpoint 4096 2797)/2)
    have hp : upperPayment 2796 = (186770072091:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2796+point split endpoint 4096 2797)/2 = (646483527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646483527:ℝ)/168755200)*ClassicalSixthBranch.v ((646483527:ℝ)/168755200)/ClassicalSixthBranch.r = (98124948547905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2796
  · change upperPayment 2797 ≤ upperValue ((point split endpoint 4096 2797+point split endpoint 4096 2798)/2)
    have hp : upperPayment 2797 = (186648825696:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2797+point split endpoint 4096 2798)/2 = (646508677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646508677:ℝ)/168755200)*ClassicalSixthBranch.v ((646508677:ℝ)/168755200)/ClassicalSixthBranch.r = (98104592560425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2797
  · change upperPayment 2798 ≤ upperValue ((point split endpoint 4096 2798+point split endpoint 4096 2799)/2)
    have hp : upperPayment 2798 = (186527548218:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2798+point split endpoint 4096 2799)/2 = (646533827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646533827:ℝ)/168755200)*ClassicalSixthBranch.v ((646533827:ℝ)/168755200)/ClassicalSixthBranch.r = (98084238597017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2798
  · change upperPayment 2799 ≤ upperValue ((point split endpoint 4096 2799+point split endpoint 4096 2800)/2)
    have hp : upperPayment 2799 = (186406239650:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2799+point split endpoint 4096 2800)/2 = (646558977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646558977:ℝ)/168755200)*ClassicalSixthBranch.v ((646558977:ℝ)/168755200)/ClassicalSixthBranch.r = (98063886657681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2799
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_174
