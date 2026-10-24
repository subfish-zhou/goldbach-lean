import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints156
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_156 (j : Fin 16) : upperPayment (16*156+j.val) ≤
    upperValue ((point split endpoint 4096 (16*156+j.val)+point split endpoint 4096 (16*156+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2496 ≤ upperValue ((point split endpoint 4096 2496+point split endpoint 4096 2497)/2)
    have hp : upperPayment 2496 = (221772048905:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2496+point split endpoint 4096 2497)/2 = (638938527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638938527:ℝ)/168755200)*ClassicalSixthBranch.v ((638938527:ℝ)/168755200)/ClassicalSixthBranch.r = (104323131642705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2496
  · change upperPayment 2497 ≤ upperValue ((point split endpoint 4096 2497+point split endpoint 4096 2498)/2)
    have hp : upperPayment 2497 = (221659818041:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2497+point split endpoint 4096 2498)/2 = (638963677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638963677:ℝ)/168755200)*ClassicalSixthBranch.v ((638963677:ℝ)/168755200)/ClassicalSixthBranch.r = (104302168433625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2497
  · change upperPayment 2498 ≤ upperValue ((point split endpoint 4096 2498+point split endpoint 4096 2499)/2)
    have hp : upperPayment 2498 = (221547558109:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2498+point split endpoint 4096 2499)/2 = (638988827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638988827:ℝ)/168755200)*ClassicalSixthBranch.v ((638988827:ℝ)/168755200)/ClassicalSixthBranch.r = (104281207248617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2498
  · change upperPayment 2499 ≤ upperValue ((point split endpoint 4096 2499+point split endpoint 4096 2500)/2)
    have hp : upperPayment 2499 = (221435269103:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2499+point split endpoint 4096 2500)/2 = (639013977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639013977:ℝ)/168755200)*ClassicalSixthBranch.v ((639013977:ℝ)/168755200)/ClassicalSixthBranch.r = (1012235418327:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2499
  · change upperPayment 2500 ≤ upperValue ((point split endpoint 4096 2500+point split endpoint 4096 2501)/2)
    have hp : upperPayment 2500 = (221322951016:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2500+point split endpoint 4096 2501)/2 = (639039127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639039127:ℝ)/168755200)*ClassicalSixthBranch.v ((639039127:ℝ)/168755200)/ClassicalSixthBranch.r = (104239290950817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2500
  · change upperPayment 2501 ≤ upperValue ((point split endpoint 4096 2501+point split endpoint 4096 2502)/2)
    have hp : upperPayment 2501 = (221210603842:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2501+point split endpoint 4096 2502)/2 = (639064277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639064277:ℝ)/168755200)*ClassicalSixthBranch.v ((639064277:ℝ)/168755200)/ClassicalSixthBranch.r = (104218335838025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2501
  · change upperPayment 2502 ≤ upperValue ((point split endpoint 4096 2502+point split endpoint 4096 2503)/2)
    have hp : upperPayment 2502 = (221098227575:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2502+point split endpoint 4096 2503)/2 = (639089427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639089427:ℝ)/168755200)*ClassicalSixthBranch.v ((639089427:ℝ)/168755200)/ClassicalSixthBranch.r = (104197382749305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2502
  · change upperPayment 2503 ≤ upperValue ((point split endpoint 4096 2503+point split endpoint 4096 2504)/2)
    have hp : upperPayment 2503 = (220985822208:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2503+point split endpoint 4096 2504)/2 = (639114577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639114577:ℝ)/168755200)*ClassicalSixthBranch.v ((639114577:ℝ)/168755200)/ClassicalSixthBranch.r = (104176431684657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2503
  · change upperPayment 2504 ≤ upperValue ((point split endpoint 4096 2504+point split endpoint 4096 2505)/2)
    have hp : upperPayment 2504 = (220873387736:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2504+point split endpoint 4096 2505)/2 = (639139727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639139727:ℝ)/168755200)*ClassicalSixthBranch.v ((639139727:ℝ)/168755200)/ClassicalSixthBranch.r = (104155482644081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2504
  · change upperPayment 2505 ≤ upperValue ((point split endpoint 4096 2505+point split endpoint 4096 2506)/2)
    have hp : upperPayment 2505 = (220760924151:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2505+point split endpoint 4096 2506)/2 = (639164877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639164877:ℝ)/168755200)*ClassicalSixthBranch.v ((639164877:ℝ)/168755200)/ClassicalSixthBranch.r = (104134535627577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2505
  · change upperPayment 2506 ≤ upperValue ((point split endpoint 4096 2506+point split endpoint 4096 2507)/2)
    have hp : upperPayment 2506 = (220648431447:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2506+point split endpoint 4096 2507)/2 = (639190027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639190027:ℝ)/168755200)*ClassicalSixthBranch.v ((639190027:ℝ)/168755200)/ClassicalSixthBranch.r = (104113590635145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2506
  · change upperPayment 2507 ≤ upperValue ((point split endpoint 4096 2507+point split endpoint 4096 2508)/2)
    have hp : upperPayment 2507 = (220535909619:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2507+point split endpoint 4096 2508)/2 = (639215177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639215177:ℝ)/168755200)*ClassicalSixthBranch.v ((639215177:ℝ)/168755200)/ClassicalSixthBranch.r = (104092647666785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2507
  · change upperPayment 2508 ≤ upperValue ((point split endpoint 4096 2508+point split endpoint 4096 2509)/2)
    have hp : upperPayment 2508 = (220423358659:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2508+point split endpoint 4096 2509)/2 = (639240327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639240327:ℝ)/168755200)*ClassicalSixthBranch.v ((639240327:ℝ)/168755200)/ClassicalSixthBranch.r = (104071706722497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2508
  · change upperPayment 2509 ≤ upperValue ((point split endpoint 4096 2509+point split endpoint 4096 2510)/2)
    have hp : upperPayment 2509 = (220310778562:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2509+point split endpoint 4096 2510)/2 = (639265477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639265477:ℝ)/168755200)*ClassicalSixthBranch.v ((639265477:ℝ)/168755200)/ClassicalSixthBranch.r = (104050767802281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2509
  · change upperPayment 2510 ≤ upperValue ((point split endpoint 4096 2510+point split endpoint 4096 2511)/2)
    have hp : upperPayment 2510 = (220198169321:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2510+point split endpoint 4096 2511)/2 = (639290627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639290627:ℝ)/168755200)*ClassicalSixthBranch.v ((639290627:ℝ)/168755200)/ClassicalSixthBranch.r = (104029830906137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2510
  · change upperPayment 2511 ≤ upperValue ((point split endpoint 4096 2511+point split endpoint 4096 2512)/2)
    have hp : upperPayment 2511 = (220085530929:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2511+point split endpoint 4096 2512)/2 = (639315777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639315777:ℝ)/168755200)*ClassicalSixthBranch.v ((639315777:ℝ)/168755200)/ClassicalSixthBranch.r = (104008896034065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2511
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_156
