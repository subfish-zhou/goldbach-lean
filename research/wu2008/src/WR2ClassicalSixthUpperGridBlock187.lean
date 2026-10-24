import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints187
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_187 (j : Fin 16) : upperPayment (16*187+j.val) ≤
    upperValue ((point split endpoint 4096 (16*187+j.val)+point split endpoint 4096 (16*187+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2992 ≤ upperValue ((point split endpoint 4096 2992+point split endpoint 4096 2993)/2)
    have hp : upperPayment 2992 = (162402799299:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2992+point split endpoint 4096 2993)/2 = (651412927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651412927:ℝ)/168755200)*ClassicalSixthBranch.v ((651412927:ℝ)/168755200)/ClassicalSixthBranch.r = (94173855017745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2992
  · change upperPayment 2993 ≤ upperValue ((point split endpoint 4096 2993+point split endpoint 4096 2994)/2)
    have hp : upperPayment 2993 = (162275320767:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2993+point split endpoint 4096 2994)/2 = (651438077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651438077:ℝ)/168755200)*ClassicalSixthBranch.v ((651438077:ℝ)/168755200)/ClassicalSixthBranch.r = (94153895748377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2993
  · change upperPayment 2994 ≤ upperValue ((point split endpoint 4096 2994+point split endpoint 4096 2995)/2)
    have hp : upperPayment 2994 = (162147809698:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2994+point split endpoint 4096 2995)/2 = (651463227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651463227:ℝ)/168755200)*ClassicalSixthBranch.v ((651463227:ℝ)/168755200)/ClassicalSixthBranch.r = (94133938503081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2994
  · change upperPayment 2995 ≤ upperValue ((point split endpoint 4096 2995+point split endpoint 4096 2996)/2)
    have hp : upperPayment 2995 = (162020266084:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2995+point split endpoint 4096 2996)/2 = (651488377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651488377:ℝ)/168755200)*ClassicalSixthBranch.v ((651488377:ℝ)/168755200)/ClassicalSixthBranch.r = (94113983281857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2995
  · change upperPayment 2996 ≤ upperValue ((point split endpoint 4096 2996+point split endpoint 4096 2997)/2)
    have hp : upperPayment 2996 = (161892689918:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2996+point split endpoint 4096 2997)/2 = (651513527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651513527:ℝ)/168755200)*ClassicalSixthBranch.v ((651513527:ℝ)/168755200)/ClassicalSixthBranch.r = (94094030084705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2996
  · change upperPayment 2997 ≤ upperValue ((point split endpoint 4096 2997+point split endpoint 4096 2998)/2)
    have hp : upperPayment 2997 = (161765081191:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2997+point split endpoint 4096 2998)/2 = (651538677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651538677:ℝ)/168755200)*ClassicalSixthBranch.v ((651538677:ℝ)/168755200)/ClassicalSixthBranch.r = (94074078911625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2997
  · change upperPayment 2998 ≤ upperValue ((point split endpoint 4096 2998+point split endpoint 4096 2999)/2)
    have hp : upperPayment 2998 = (161637439897:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2998+point split endpoint 4096 2999)/2 = (651563827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651563827:ℝ)/168755200)*ClassicalSixthBranch.v ((651563827:ℝ)/168755200)/ClassicalSixthBranch.r = (94054129762617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2998
  · change upperPayment 2999 ≤ upperValue ((point split endpoint 4096 2999+point split endpoint 4096 3000)/2)
    have hp : upperPayment 2999 = (161509766027:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2999+point split endpoint 4096 3000)/2 = (651588977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651588977:ℝ)/168755200)*ClassicalSixthBranch.v ((651588977:ℝ)/168755200)/ClassicalSixthBranch.r = (94034182637681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2999
  · change upperPayment 3000 ≤ upperValue ((point split endpoint 4096 3000+point split endpoint 4096 3001)/2)
    have hp : upperPayment 3000 = (161382059573:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3000+point split endpoint 4096 3001)/2 = (651614127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651614127:ℝ)/168755200)*ClassicalSixthBranch.v ((651614127:ℝ)/168755200)/ClassicalSixthBranch.r = (94014237536817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3000
  · change upperPayment 3001 ≤ upperValue ((point split endpoint 4096 3001+point split endpoint 4096 3002)/2)
    have hp : upperPayment 3001 = (161254320528:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3001+point split endpoint 4096 3002)/2 = (651639277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651639277:ℝ)/168755200)*ClassicalSixthBranch.v ((651639277:ℝ)/168755200)/ClassicalSixthBranch.r = (93994294460025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3001
  · change upperPayment 3002 ≤ upperValue ((point split endpoint 4096 3002+point split endpoint 4096 3003)/2)
    have hp : upperPayment 3002 = (161126548885:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3002+point split endpoint 4096 3003)/2 = (651664427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651664427:ℝ)/168755200)*ClassicalSixthBranch.v ((651664427:ℝ)/168755200)/ClassicalSixthBranch.r = (93974353407305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3002
  · change upperPayment 3003 ≤ upperValue ((point split endpoint 4096 3003+point split endpoint 4096 3004)/2)
    have hp : upperPayment 3003 = (160998744634:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3003+point split endpoint 4096 3004)/2 = (651689577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651689577:ℝ)/168755200)*ClassicalSixthBranch.v ((651689577:ℝ)/168755200)/ClassicalSixthBranch.r = (93954414378657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3003
  · change upperPayment 3004 ≤ upperValue ((point split endpoint 4096 3004+point split endpoint 4096 3005)/2)
    have hp : upperPayment 3004 = (160870907770:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3004+point split endpoint 4096 3005)/2 = (651714727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651714727:ℝ)/168755200)*ClassicalSixthBranch.v ((651714727:ℝ)/168755200)/ClassicalSixthBranch.r = (93934477374081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3004
  · change upperPayment 3005 ≤ upperValue ((point split endpoint 4096 3005+point split endpoint 4096 3006)/2)
    have hp : upperPayment 3005 = (160743038283:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3005+point split endpoint 4096 3006)/2 = (651739877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651739877:ℝ)/168755200)*ClassicalSixthBranch.v ((651739877:ℝ)/168755200)/ClassicalSixthBranch.r = (93914542393577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3005
  · change upperPayment 3006 ≤ upperValue ((point split endpoint 4096 3006+point split endpoint 4096 3007)/2)
    have hp : upperPayment 3006 = (160615136166:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3006+point split endpoint 4096 3007)/2 = (651765027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651765027:ℝ)/168755200)*ClassicalSixthBranch.v ((651765027:ℝ)/168755200)/ClassicalSixthBranch.r = (93894609437145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3006
  · change upperPayment 3007 ≤ upperValue ((point split endpoint 4096 3007+point split endpoint 4096 3008)/2)
    have hp : upperPayment 3007 = (160487201412:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3007+point split endpoint 4096 3008)/2 = (651790177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651790177:ℝ)/168755200)*ClassicalSixthBranch.v ((651790177:ℝ)/168755200)/ClassicalSixthBranch.r = (93874678504785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3007
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_187
