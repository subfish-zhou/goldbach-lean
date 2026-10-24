import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints229
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_229 (j : Fin 16) : upperPayment (16*229+j.val) ≤
    upperValue ((point split endpoint 4096 (16*229+j.val)+point split endpoint 4096 (16*229+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3664 ≤ upperValue ((point split endpoint 4096 3664+point split endpoint 4096 3665)/2)
    have hp : upperPayment 3664 = (68984792706:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3664+point split endpoint 4096 3665)/2 = (668313727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668313727:ℝ)/168755200)*ClassicalSixthBranch.v ((668313727:ℝ)/168755200)/ClassicalSixthBranch.r = (81217565179281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3664
  · change upperPayment 3665 ≤ upperValue ((point split endpoint 4096 3665+point split endpoint 4096 3666)/2)
    have hp : upperPayment 3665 = (68833538354:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3665+point split endpoint 4096 3666)/2 = (668338877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668338877:ℝ)/168755200)*ClassicalSixthBranch.v ((668338877:ℝ)/168755200)/ClassicalSixthBranch.r = (81198966086297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3665
  · change upperPayment 3666 ≤ upperValue ((point split endpoint 4096 3666+point split endpoint 4096 3667)/2)
    have hp : upperPayment 3666 = (68682245493:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3666+point split endpoint 4096 3667)/2 = (668364027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668364027:ℝ)/168755200)*ClassicalSixthBranch.v ((668364027:ℝ)/168755200)/ClassicalSixthBranch.r = (81180369017385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3666
  · change upperPayment 3667 ≤ upperValue ((point split endpoint 4096 3667+point split endpoint 4096 3668)/2)
    have hp : upperPayment 3667 = (68530914112:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3667+point split endpoint 4096 3668)/2 = (668389177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668389177:ℝ)/168755200)*ClassicalSixthBranch.v ((668389177:ℝ)/168755200)/ClassicalSixthBranch.r = (81161773972545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3667
  · change upperPayment 3668 ≤ upperValue ((point split endpoint 4096 3668+point split endpoint 4096 3669)/2)
    have hp : upperPayment 3668 = (68379544203:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3668+point split endpoint 4096 3669)/2 = (668414327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668414327:ℝ)/168755200)*ClassicalSixthBranch.v ((668414327:ℝ)/168755200)/ClassicalSixthBranch.r = (81143180951777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3668
  · change upperPayment 3669 ≤ upperValue ((point split endpoint 4096 3669+point split endpoint 4096 3670)/2)
    have hp : upperPayment 3669 = (68228135754:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3669+point split endpoint 4096 3670)/2 = (668439477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668439477:ℝ)/168755200)*ClassicalSixthBranch.v ((668439477:ℝ)/168755200)/ClassicalSixthBranch.r = (81124589955081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3669
  · change upperPayment 3670 ≤ upperValue ((point split endpoint 4096 3670+point split endpoint 4096 3671)/2)
    have hp : upperPayment 3670 = (68076688756:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3670+point split endpoint 4096 3671)/2 = (668464627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668464627:ℝ)/168755200)*ClassicalSixthBranch.v ((668464627:ℝ)/168755200)/ClassicalSixthBranch.r = (81106000982457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3670
  · change upperPayment 3671 ≤ upperValue ((point split endpoint 4096 3671+point split endpoint 4096 3672)/2)
    have hp : upperPayment 3671 = (67925203198:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3671+point split endpoint 4096 3672)/2 = (668489777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668489777:ℝ)/168755200)*ClassicalSixthBranch.v ((668489777:ℝ)/168755200)/ClassicalSixthBranch.r = (81087414033905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3671
  · change upperPayment 3672 ≤ upperValue ((point split endpoint 4096 3672+point split endpoint 4096 3673)/2)
    have hp : upperPayment 3672 = (67773679070:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3672+point split endpoint 4096 3673)/2 = (668514927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668514927:ℝ)/168755200)*ClassicalSixthBranch.v ((668514927:ℝ)/168755200)/ClassicalSixthBranch.r = (81068829109425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3672
  · change upperPayment 3673 ≤ upperValue ((point split endpoint 4096 3673+point split endpoint 4096 3674)/2)
    have hp : upperPayment 3673 = (67622116362:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3673+point split endpoint 4096 3674)/2 = (668540077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668540077:ℝ)/168755200)*ClassicalSixthBranch.v ((668540077:ℝ)/168755200)/ClassicalSixthBranch.r = (81050246209017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3673
  · change upperPayment 3674 ≤ upperValue ((point split endpoint 4096 3674+point split endpoint 4096 3675)/2)
    have hp : upperPayment 3674 = (67470515064:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3674+point split endpoint 4096 3675)/2 = (668565227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668565227:ℝ)/168755200)*ClassicalSixthBranch.v ((668565227:ℝ)/168755200)/ClassicalSixthBranch.r = (81031665332681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3674
  · change upperPayment 3675 ≤ upperValue ((point split endpoint 4096 3675+point split endpoint 4096 3676)/2)
    have hp : upperPayment 3675 = (67318875165:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3675+point split endpoint 4096 3676)/2 = (668590377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668590377:ℝ)/168755200)*ClassicalSixthBranch.v ((668590377:ℝ)/168755200)/ClassicalSixthBranch.r = (81013086480417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3675
  · change upperPayment 3676 ≤ upperValue ((point split endpoint 4096 3676+point split endpoint 4096 3677)/2)
    have hp : upperPayment 3676 = (67167196655:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3676+point split endpoint 4096 3677)/2 = (668615527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668615527:ℝ)/168755200)*ClassicalSixthBranch.v ((668615527:ℝ)/168755200)/ClassicalSixthBranch.r = (80994509652225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3676
  · change upperPayment 3677 ≤ upperValue ((point split endpoint 4096 3677+point split endpoint 4096 3678)/2)
    have hp : upperPayment 3677 = (67015479524:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3677+point split endpoint 4096 3678)/2 = (668640677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668640677:ℝ)/168755200)*ClassicalSixthBranch.v ((668640677:ℝ)/168755200)/ClassicalSixthBranch.r = (80975934848105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3677
  · change upperPayment 3678 ≤ upperValue ((point split endpoint 4096 3678+point split endpoint 4096 3679)/2)
    have hp : upperPayment 3678 = (66863723762:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3678+point split endpoint 4096 3679)/2 = (668665827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668665827:ℝ)/168755200)*ClassicalSixthBranch.v ((668665827:ℝ)/168755200)/ClassicalSixthBranch.r = (80957362068057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3678
  · change upperPayment 3679 ≤ upperValue ((point split endpoint 4096 3679+point split endpoint 4096 3680)/2)
    have hp : upperPayment 3679 = (66711929358:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3679+point split endpoint 4096 3680)/2 = (668690977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668690977:ℝ)/168755200)*ClassicalSixthBranch.v ((668690977:ℝ)/168755200)/ClassicalSixthBranch.r = (80938791312081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3679
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_229
