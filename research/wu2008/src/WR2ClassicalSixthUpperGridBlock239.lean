import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints239
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_239 (j : Fin 16) : upperPayment (16*239+j.val) ≤
    upperValue ((point split endpoint 4096 (16*239+j.val)+point split endpoint 4096 (16*239+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3824 ≤ upperValue ((point split endpoint 4096 3824+point split endpoint 4096 3825)/2)
    have hp : upperPayment 3824 = (44287326282:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3824+point split endpoint 4096 3825)/2 = (672337727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672337727:ℝ)/168755200)*ClassicalSixthBranch.v ((672337727:ℝ)/168755200)/ClassicalSixthBranch.r = (78267456497681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3824
  · change upperPayment 3825 ≤ upperValue ((point split endpoint 4096 3825+point split endpoint 4096 3826)/2)
    have hp : upperPayment 3825 = (44129778028:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3825+point split endpoint 4096 3826)/2 = (672362877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672362877:ℝ)/168755200)*ClassicalSixthBranch.v ((672362877:ℝ)/168755200)/ClassicalSixthBranch.r = (78249181256217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3825
  · change upperPayment 3826 ≤ upperValue ((point split endpoint 4096 3826+point split endpoint 4096 3827)/2)
    have hp : upperPayment 3826 = (43972189579:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3826+point split endpoint 4096 3827)/2 = (672388027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672388027:ℝ)/168755200)*ClassicalSixthBranch.v ((672388027:ℝ)/168755200)/ClassicalSixthBranch.r = (78230908038825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3826
  · change upperPayment 3827 ≤ upperValue ((point split endpoint 4096 3827+point split endpoint 4096 3828)/2)
    have hp : upperPayment 3827 = (43814560925:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3827+point split endpoint 4096 3828)/2 = (672413177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672413177:ℝ)/168755200)*ClassicalSixthBranch.v ((672413177:ℝ)/168755200)/ClassicalSixthBranch.r = (78212636845505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3827
  · change upperPayment 3828 ≤ upperValue ((point split endpoint 4096 3828+point split endpoint 4096 3829)/2)
    have hp : upperPayment 3828 = (43656892054:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3828+point split endpoint 4096 3829)/2 = (672438327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672438327:ℝ)/168755200)*ClassicalSixthBranch.v ((672438327:ℝ)/168755200)/ClassicalSixthBranch.r = (78194367676257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3828
  · change upperPayment 3829 ≤ upperValue ((point split endpoint 4096 3829+point split endpoint 4096 3830)/2)
    have hp : upperPayment 3829 = (43499182956:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3829+point split endpoint 4096 3830)/2 = (672463477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672463477:ℝ)/168755200)*ClassicalSixthBranch.v ((672463477:ℝ)/168755200)/ClassicalSixthBranch.r = (78176100531081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3829
  · change upperPayment 3830 ≤ upperValue ((point split endpoint 4096 3830+point split endpoint 4096 3831)/2)
    have hp : upperPayment 3830 = (43341433620:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3830+point split endpoint 4096 3831)/2 = (672488627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672488627:ℝ)/168755200)*ClassicalSixthBranch.v ((672488627:ℝ)/168755200)/ClassicalSixthBranch.r = (78157835409977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3830
  · change upperPayment 3831 ≤ upperValue ((point split endpoint 4096 3831+point split endpoint 4096 3832)/2)
    have hp : upperPayment 3831 = (43183644035:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3831+point split endpoint 4096 3832)/2 = (672513777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672513777:ℝ)/168755200)*ClassicalSixthBranch.v ((672513777:ℝ)/168755200)/ClassicalSixthBranch.r = (78139572312945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3831
  · change upperPayment 3832 ≤ upperValue ((point split endpoint 4096 3832+point split endpoint 4096 3833)/2)
    have hp : upperPayment 3832 = (43025814189:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3832+point split endpoint 4096 3833)/2 = (672538927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672538927:ℝ)/168755200)*ClassicalSixthBranch.v ((672538927:ℝ)/168755200)/ClassicalSixthBranch.r = (78121311239985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3832
  · change upperPayment 3833 ≤ upperValue ((point split endpoint 4096 3833+point split endpoint 4096 3834)/2)
    have hp : upperPayment 3833 = (42867944073:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3833+point split endpoint 4096 3834)/2 = (672564077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672564077:ℝ)/168755200)*ClassicalSixthBranch.v ((672564077:ℝ)/168755200)/ClassicalSixthBranch.r = (78103052191097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3833
  · change upperPayment 3834 ≤ upperValue ((point split endpoint 4096 3834+point split endpoint 4096 3835)/2)
    have hp : upperPayment 3834 = (42710033675:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3834+point split endpoint 4096 3835)/2 = (672589227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672589227:ℝ)/168755200)*ClassicalSixthBranch.v ((672589227:ℝ)/168755200)/ClassicalSixthBranch.r = (78084795166281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3834
  · change upperPayment 3835 ≤ upperValue ((point split endpoint 4096 3835+point split endpoint 4096 3836)/2)
    have hp : upperPayment 3835 = (42552082984:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3835+point split endpoint 4096 3836)/2 = (672614377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672614377:ℝ)/168755200)*ClassicalSixthBranch.v ((672614377:ℝ)/168755200)/ClassicalSixthBranch.r = (78066540165537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3835
  · change upperPayment 3836 ≤ upperValue ((point split endpoint 4096 3836+point split endpoint 4096 3837)/2)
    have hp : upperPayment 3836 = (42394091989:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3836+point split endpoint 4096 3837)/2 = (672639527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672639527:ℝ)/168755200)*ClassicalSixthBranch.v ((672639527:ℝ)/168755200)/ClassicalSixthBranch.r = (78048287188865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3836
  · change upperPayment 3837 ≤ upperValue ((point split endpoint 4096 3837+point split endpoint 4096 3838)/2)
    have hp : upperPayment 3837 = (42236060679:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3837+point split endpoint 4096 3838)/2 = (672664677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672664677:ℝ)/168755200)*ClassicalSixthBranch.v ((672664677:ℝ)/168755200)/ClassicalSixthBranch.r = (78030036236265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3837
  · change upperPayment 3838 ≤ upperValue ((point split endpoint 4096 3838+point split endpoint 4096 3839)/2)
    have hp : upperPayment 3838 = (42077989044:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3838+point split endpoint 4096 3839)/2 = (672689827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672689827:ℝ)/168755200)*ClassicalSixthBranch.v ((672689827:ℝ)/168755200)/ClassicalSixthBranch.r = (757395993279:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3838
  · change upperPayment 3839 ≤ upperValue ((point split endpoint 4096 3839+point split endpoint 4096 3840)/2)
    have hp : upperPayment 3839 = (41919877072:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3839+point split endpoint 4096 3840)/2 = (672714977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672714977:ℝ)/168755200)*ClassicalSixthBranch.v ((672714977:ℝ)/168755200)/ClassicalSixthBranch.r = (77993540403281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3839
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_239
