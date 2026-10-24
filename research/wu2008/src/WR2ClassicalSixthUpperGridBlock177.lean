import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints177
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_177 (j : Fin 16) : upperPayment (16*177+j.val) ≤
    upperValue ((point split endpoint 4096 (16*177+j.val)+point split endpoint 4096 (16*177+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2832 ≤ upperValue ((point split endpoint 4096 2832+point split endpoint 4096 2833)/2)
    have hp : upperPayment 2832 = (182385568613:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2832+point split endpoint 4096 2833)/2 = (647388927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647388927:ℝ)/168755200)*ClassicalSixthBranch.v ((647388927:ℝ)/168755200)/ClassicalSixthBranch.r = (97393408163985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2832
  · change upperPayment 2833 ≤ upperValue ((point split endpoint 4096 2833+point split endpoint 4096 2834)/2)
    have hp : upperPayment 2833 = (182263198724:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2833+point split endpoint 4096 2834)/2 = (647414077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647414077:ℝ)/168755200)*ClassicalSixthBranch.v ((647414077:ℝ)/168755200)/ClassicalSixthBranch.r = (97373125043097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2833
  · change upperPayment 2834 ≤ upperValue ((point split endpoint 4096 2834+point split endpoint 4096 2835)/2)
    have hp : upperPayment 2834 = (182140797493:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2834+point split endpoint 4096 2835)/2 = (647439227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647439227:ℝ)/168755200)*ClassicalSixthBranch.v ((647439227:ℝ)/168755200)/ClassicalSixthBranch.r = (97352843946281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2834
  · change upperPayment 2835 ≤ upperValue ((point split endpoint 4096 2835+point split endpoint 4096 2836)/2)
    have hp : upperPayment 2835 = (182018364914:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2835+point split endpoint 4096 2836)/2 = (647464377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647464377:ℝ)/168755200)*ClassicalSixthBranch.v ((647464377:ℝ)/168755200)/ClassicalSixthBranch.r = (97332564873537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2835
  · change upperPayment 2836 ≤ upperValue ((point split endpoint 4096 2836+point split endpoint 4096 2837)/2)
    have hp : upperPayment 2836 = (181895900979:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2836+point split endpoint 4096 2837)/2 = (647489527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647489527:ℝ)/168755200)*ClassicalSixthBranch.v ((647489527:ℝ)/168755200)/ClassicalSixthBranch.r = (97312287824865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2836
  · change upperPayment 2837 ≤ upperValue ((point split endpoint 4096 2837+point split endpoint 4096 2838)/2)
    have hp : upperPayment 2837 = (181773405681:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2837+point split endpoint 4096 2838)/2 = (647514677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647514677:ℝ)/168755200)*ClassicalSixthBranch.v ((647514677:ℝ)/168755200)/ClassicalSixthBranch.r = (97292012800265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2837
  · change upperPayment 2838 ≤ upperValue ((point split endpoint 4096 2838+point split endpoint 4096 2839)/2)
    have hp : upperPayment 2838 = (181650879013:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2838+point split endpoint 4096 2839)/2 = (647539827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647539827:ℝ)/168755200)*ClassicalSixthBranch.v ((647539827:ℝ)/168755200)/ClassicalSixthBranch.r = (97271739799737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2838
  · change upperPayment 2839 ≤ upperValue ((point split endpoint 4096 2839+point split endpoint 4096 2840)/2)
    have hp : upperPayment 2839 = (181528320967:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2839+point split endpoint 4096 2840)/2 = (647564977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647564977:ℝ)/168755200)*ClassicalSixthBranch.v ((647564977:ℝ)/168755200)/ClassicalSixthBranch.r = (97251468823281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2839
  · change upperPayment 2840 ≤ upperValue ((point split endpoint 4096 2840+point split endpoint 4096 2841)/2)
    have hp : upperPayment 2840 = (181405731536:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2840+point split endpoint 4096 2841)/2 = (647590127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647590127:ℝ)/168755200)*ClassicalSixthBranch.v ((647590127:ℝ)/168755200)/ClassicalSixthBranch.r = (97231199870897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2840
  · change upperPayment 2841 ≤ upperValue ((point split endpoint 4096 2841+point split endpoint 4096 2842)/2)
    have hp : upperPayment 2841 = (181283110713:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2841+point split endpoint 4096 2842)/2 = (647615277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647615277:ℝ)/168755200)*ClassicalSixthBranch.v ((647615277:ℝ)/168755200)/ClassicalSixthBranch.r = (97210932942585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2841
  · change upperPayment 2842 ≤ upperValue ((point split endpoint 4096 2842+point split endpoint 4096 2843)/2)
    have hp : upperPayment 2842 = (181160458491:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2842+point split endpoint 4096 2843)/2 = (647640427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647640427:ℝ)/168755200)*ClassicalSixthBranch.v ((647640427:ℝ)/168755200)/ClassicalSixthBranch.r = (97190668038345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2842
  · change upperPayment 2843 ≤ upperValue ((point split endpoint 4096 2843+point split endpoint 4096 2844)/2)
    have hp : upperPayment 2843 = (181037774862:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2843+point split endpoint 4096 2844)/2 = (647665577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647665577:ℝ)/168755200)*ClassicalSixthBranch.v ((647665577:ℝ)/168755200)/ClassicalSixthBranch.r = (97170405158177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2843
  · change upperPayment 2844 ≤ upperValue ((point split endpoint 4096 2844+point split endpoint 4096 2845)/2)
    have hp : upperPayment 2844 = (180915059820:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2844+point split endpoint 4096 2845)/2 = (647690727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647690727:ℝ)/168755200)*ClassicalSixthBranch.v ((647690727:ℝ)/168755200)/ClassicalSixthBranch.r = (97150144302081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2844
  · change upperPayment 2845 ≤ upperValue ((point split endpoint 4096 2845+point split endpoint 4096 2846)/2)
    have hp : upperPayment 2845 = (180792313356:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2845+point split endpoint 4096 2846)/2 = (647715877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647715877:ℝ)/168755200)*ClassicalSixthBranch.v ((647715877:ℝ)/168755200)/ClassicalSixthBranch.r = (97129885470057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2845
  · change upperPayment 2846 ≤ upperValue ((point split endpoint 4096 2846+point split endpoint 4096 2847)/2)
    have hp : upperPayment 2846 = (180669535464:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2846+point split endpoint 4096 2847)/2 = (647741027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647741027:ℝ)/168755200)*ClassicalSixthBranch.v ((647741027:ℝ)/168755200)/ClassicalSixthBranch.r = (97109628662105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2846
  · change upperPayment 2847 ≤ upperValue ((point split endpoint 4096 2847+point split endpoint 4096 2848)/2)
    have hp : upperPayment 2847 = (180546726137:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2847+point split endpoint 4096 2848)/2 = (647766177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647766177:ℝ)/168755200)*ClassicalSixthBranch.v ((647766177:ℝ)/168755200)/ClassicalSixthBranch.r = (97089373878225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2847
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_177
