import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints218
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_218 (j : Fin 16) : upperPayment (16*218+j.val) ≤
    upperValue ((point split endpoint 4096 (16*218+j.val)+point split endpoint 4096 (16*218+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3488 ≤ upperValue ((point split endpoint 4096 3488+point split endpoint 4096 3489)/2)
    have hp : upperPayment 3488 = (95014985543:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3488+point split endpoint 4096 3489)/2 = (663887327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663887327:ℝ)/168755200)*ClassicalSixthBranch.v ((663887327:ℝ)/168755200)/ClassicalSixthBranch.r = (84522532489937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3488
  · change upperPayment 3489 ≤ upperValue ((point split endpoint 4096 3489+point split endpoint 4096 3490)/2)
    have hp : upperPayment 3489 = (94870353955:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3489+point split endpoint 4096 3490)/2 = (663912477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663912477:ℝ)/168755200)*ClassicalSixthBranch.v ((663912477:ℝ)/168755200)/ClassicalSixthBranch.r = (84503577160281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3489
  · change upperPayment 3490 ≤ upperValue ((point split endpoint 4096 3490+point split endpoint 4096 3491)/2)
    have hp : upperPayment 3490 = (94725685586:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3490+point split endpoint 4096 3491)/2 = (663937627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663937627:ℝ)/168755200)*ClassicalSixthBranch.v ((663937627:ℝ)/168755200)/ClassicalSixthBranch.r = (84484623854697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3490
  · change upperPayment 3491 ≤ upperValue ((point split endpoint 4096 3491+point split endpoint 4096 3492)/2)
    have hp : upperPayment 3491 = (94580980426:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3491+point split endpoint 4096 3492)/2 = (663962777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663962777:ℝ)/168755200)*ClassicalSixthBranch.v ((663962777:ℝ)/168755200)/ClassicalSixthBranch.r = (84465672573185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3491
  · change upperPayment 3492 ≤ upperValue ((point split endpoint 4096 3492+point split endpoint 4096 3493)/2)
    have hp : upperPayment 3492 = (94436238467:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3492+point split endpoint 4096 3493)/2 = (663987927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((663987927:ℝ)/168755200)*ClassicalSixthBranch.v ((663987927:ℝ)/168755200)/ClassicalSixthBranch.r = (84446723315745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3492
  · change upperPayment 3493 ≤ upperValue ((point split endpoint 4096 3493+point split endpoint 4096 3494)/2)
    have hp : upperPayment 3493 = (94291459698:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3493+point split endpoint 4096 3494)/2 = (664013077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664013077:ℝ)/168755200)*ClassicalSixthBranch.v ((664013077:ℝ)/168755200)/ClassicalSixthBranch.r = (84427776082377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3493
  · change upperPayment 3494 ≤ upperValue ((point split endpoint 4096 3494+point split endpoint 4096 3495)/2)
    have hp : upperPayment 3494 = (94146644110:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3494+point split endpoint 4096 3495)/2 = (664038227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664038227:ℝ)/168755200)*ClassicalSixthBranch.v ((664038227:ℝ)/168755200)/ClassicalSixthBranch.r = (84408830873081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3494
  · change upperPayment 3495 ≤ upperValue ((point split endpoint 4096 3495+point split endpoint 4096 3496)/2)
    have hp : upperPayment 3495 = (94001791694:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3495+point split endpoint 4096 3496)/2 = (664063377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664063377:ℝ)/168755200)*ClassicalSixthBranch.v ((664063377:ℝ)/168755200)/ClassicalSixthBranch.r = (84389887687857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3495
  · change upperPayment 3496 ≤ upperValue ((point split endpoint 4096 3496+point split endpoint 4096 3497)/2)
    have hp : upperPayment 3496 = (93856902441:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3496+point split endpoint 4096 3497)/2 = (664088527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664088527:ℝ)/168755200)*ClassicalSixthBranch.v ((664088527:ℝ)/168755200)/ClassicalSixthBranch.r = (84370946526705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3496
  · change upperPayment 3497 ≤ upperValue ((point split endpoint 4096 3497+point split endpoint 4096 3498)/2)
    have hp : upperPayment 3497 = (93711976340:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3497+point split endpoint 4096 3498)/2 = (664113677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664113677:ℝ)/168755200)*ClassicalSixthBranch.v ((664113677:ℝ)/168755200)/ClassicalSixthBranch.r = (84352007389625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3497
  · change upperPayment 3498 ≤ upperValue ((point split endpoint 4096 3498+point split endpoint 4096 3499)/2)
    have hp : upperPayment 3498 = (93567013382:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3498+point split endpoint 4096 3499)/2 = (664138827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664138827:ℝ)/168755200)*ClassicalSixthBranch.v ((664138827:ℝ)/168755200)/ClassicalSixthBranch.r = (84333070276617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3498
  · change upperPayment 3499 ≤ upperValue ((point split endpoint 4096 3499+point split endpoint 4096 3500)/2)
    have hp : upperPayment 3499 = (93422013558:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3499+point split endpoint 4096 3500)/2 = (664163977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664163977:ℝ)/168755200)*ClassicalSixthBranch.v ((664163977:ℝ)/168755200)/ClassicalSixthBranch.r = (84314135187681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3499
  · change upperPayment 3500 ≤ upperValue ((point split endpoint 4096 3500+point split endpoint 4096 3501)/2)
    have hp : upperPayment 3500 = (93276976859:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3500+point split endpoint 4096 3501)/2 = (664189127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664189127:ℝ)/168755200)*ClassicalSixthBranch.v ((664189127:ℝ)/168755200)/ClassicalSixthBranch.r = (84295202122817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3500
  · change upperPayment 3501 ≤ upperValue ((point split endpoint 4096 3501+point split endpoint 4096 3502)/2)
    have hp : upperPayment 3501 = (93131903274:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3501+point split endpoint 4096 3502)/2 = (664214277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664214277:ℝ)/168755200)*ClassicalSixthBranch.v ((664214277:ℝ)/168755200)/ClassicalSixthBranch.r = (84276271082025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3501
  · change upperPayment 3502 ≤ upperValue ((point split endpoint 4096 3502+point split endpoint 4096 3503)/2)
    have hp : upperPayment 3502 = (92986792794:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3502+point split endpoint 4096 3503)/2 = (664239427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664239427:ℝ)/168755200)*ClassicalSixthBranch.v ((664239427:ℝ)/168755200)/ClassicalSixthBranch.r = (84257342065305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3502
  · change upperPayment 3503 ≤ upperValue ((point split endpoint 4096 3503+point split endpoint 4096 3504)/2)
    have hp : upperPayment 3503 = (92841645410:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3503+point split endpoint 4096 3504)/2 = (664264577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((664264577:ℝ)/168755200)*ClassicalSixthBranch.v ((664264577:ℝ)/168755200)/ClassicalSixthBranch.r = (84238415072657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3503
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_218
