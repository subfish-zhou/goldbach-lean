import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints220
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_220 (j : Fin 16) : upperPayment (16*220+j.val) ≤
    upperValue ((point split endpoint 4096 (16*220+j.val)+point split endpoint 4096 (16*220+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3520 ≤ upperValue ((point split endpoint 4096 3520+point split endpoint 4096 3521)/2)
    have hp : upperPayment 3520 = (90368484297:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3520+point split endpoint 4096 3521)/2 = (664692127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664692127:ℝ)/168755200)*ClassicalSixthBranch.v ((664692127:ℝ)/168755200)/ClassicalSixthBranch.r = (83916965880657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3520
  · change upperPayment 3521 ≤ upperValue ((point split endpoint 4096 3521+point split endpoint 4096 3522)/2)
    have hp : upperPayment 3521 = (90222671005:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3521+point split endpoint 4096 3522)/2 = (664717277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664717277:ℝ)/168755200)*ClassicalSixthBranch.v ((664717277:ℝ)/168755200)/ClassicalSixthBranch.r = (83898075321305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3521
  · change upperPayment 3522 ≤ upperValue ((point split endpoint 4096 3522+point split endpoint 4096 3523)/2)
    have hp : upperPayment 3522 = (90076820628:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3522+point split endpoint 4096 3523)/2 = (664742427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664742427:ℝ)/168755200)*ClassicalSixthBranch.v ((664742427:ℝ)/168755200)/ClassicalSixthBranch.r = (83879186786025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3522
  · change upperPayment 3523 ≤ upperValue ((point split endpoint 4096 3523+point split endpoint 4096 3524)/2)
    have hp : upperPayment 3523 = (89930933156:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3523+point split endpoint 4096 3524)/2 = (664767577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664767577:ℝ)/168755200)*ClassicalSixthBranch.v ((664767577:ℝ)/168755200)/ClassicalSixthBranch.r = (83860300274817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3523
  · change upperPayment 3524 ≤ upperValue ((point split endpoint 4096 3524+point split endpoint 4096 3525)/2)
    have hp : upperPayment 3524 = (89785008578:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3524+point split endpoint 4096 3525)/2 = (664792727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664792727:ℝ)/168755200)*ClassicalSixthBranch.v ((664792727:ℝ)/168755200)/ClassicalSixthBranch.r = (83841415787681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3524
  · change upperPayment 3525 ≤ upperValue ((point split endpoint 4096 3525+point split endpoint 4096 3526)/2)
    have hp : upperPayment 3525 = (89639046887:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3525+point split endpoint 4096 3526)/2 = (664817877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664817877:ℝ)/168755200)*ClassicalSixthBranch.v ((664817877:ℝ)/168755200)/ClassicalSixthBranch.r = (83822533324617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3525
  · change upperPayment 3526 ≤ upperValue ((point split endpoint 4096 3526+point split endpoint 4096 3527)/2)
    have hp : upperPayment 3526 = (89493048071:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3526+point split endpoint 4096 3527)/2 = (664843027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664843027:ℝ)/168755200)*ClassicalSixthBranch.v ((664843027:ℝ)/168755200)/ClassicalSixthBranch.r = (83803652885625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3526
  · change upperPayment 3527 ≤ upperValue ((point split endpoint 4096 3527+point split endpoint 4096 3528)/2)
    have hp : upperPayment 3527 = (89347012121:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3527+point split endpoint 4096 3528)/2 = (664868177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664868177:ℝ)/168755200)*ClassicalSixthBranch.v ((664868177:ℝ)/168755200)/ClassicalSixthBranch.r = (83784774470705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3527
  · change upperPayment 3528 ≤ upperValue ((point split endpoint 4096 3528+point split endpoint 4096 3529)/2)
    have hp : upperPayment 3528 = (89200939028:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3528+point split endpoint 4096 3529)/2 = (664893327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664893327:ℝ)/168755200)*ClassicalSixthBranch.v ((664893327:ℝ)/168755200)/ClassicalSixthBranch.r = (83765898079857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3528
  · change upperPayment 3529 ≤ upperValue ((point split endpoint 4096 3529+point split endpoint 4096 3530)/2)
    have hp : upperPayment 3529 = (89054828782:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3529+point split endpoint 4096 3530)/2 = (664918477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664918477:ℝ)/168755200)*ClassicalSixthBranch.v ((664918477:ℝ)/168755200)/ClassicalSixthBranch.r = (813077900127:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3529
  · change upperPayment 3530 ≤ upperValue ((point split endpoint 4096 3530+point split endpoint 4096 3531)/2)
    have hp : upperPayment 3530 = (88908681374:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3530+point split endpoint 4096 3531)/2 = (664943627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664943627:ℝ)/168755200)*ClassicalSixthBranch.v ((664943627:ℝ)/168755200)/ClassicalSixthBranch.r = (83728151370377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3530
  · change upperPayment 3531 ≤ upperValue ((point split endpoint 4096 3531+point split endpoint 4096 3532)/2)
    have hp : upperPayment 3531 = (88762496793:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3531+point split endpoint 4096 3532)/2 = (664968777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664968777:ℝ)/168755200)*ClassicalSixthBranch.v ((664968777:ℝ)/168755200)/ClassicalSixthBranch.r = (83709281051745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3531
  · change upperPayment 3532 ≤ upperValue ((point split endpoint 4096 3532+point split endpoint 4096 3533)/2)
    have hp : upperPayment 3532 = (88616275031:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3532+point split endpoint 4096 3533)/2 = (664993927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664993927:ℝ)/168755200)*ClassicalSixthBranch.v ((664993927:ℝ)/168755200)/ClassicalSixthBranch.r = (83690412757185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3532
  · change upperPayment 3533 ≤ upperValue ((point split endpoint 4096 3533+point split endpoint 4096 3534)/2)
    have hp : upperPayment 3533 = (88470016077:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3533+point split endpoint 4096 3534)/2 = (665019077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665019077:ℝ)/168755200)*ClassicalSixthBranch.v ((665019077:ℝ)/168755200)/ClassicalSixthBranch.r = (83671546486697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3533
  · change upperPayment 3534 ≤ upperValue ((point split endpoint 4096 3534+point split endpoint 4096 3535)/2)
    have hp : upperPayment 3534 = (88323719922:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3534+point split endpoint 4096 3535)/2 = (665044227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665044227:ℝ)/168755200)*ClassicalSixthBranch.v ((665044227:ℝ)/168755200)/ClassicalSixthBranch.r = (83652682240281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3534
  · change upperPayment 3535 ≤ upperValue ((point split endpoint 4096 3535+point split endpoint 4096 3536)/2)
    have hp : upperPayment 3535 = (88177386557:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3535+point split endpoint 4096 3536)/2 = (665069377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((665069377:ℝ)/168755200)*ClassicalSixthBranch.v ((665069377:ℝ)/168755200)/ClassicalSixthBranch.r = (83633820017937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3535
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_220
