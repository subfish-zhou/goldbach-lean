import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints158
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_158 (j : Fin 16) : upperPayment (16*158+j.val) ≤
    upperValue ((point split endpoint 4096 (16*158+j.val)+point split endpoint 4096 (16*158+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2528 ≤ upperValue ((point split endpoint 4096 2528+point split endpoint 4096 2529)/2)
    have hp : upperPayment 2528 = (218166212106:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2528+point split endpoint 4096 2529)/2 = (639743327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639743327:ℝ)/168755200)*ClassicalSixthBranch.v ((639743327:ℝ)/168755200)/ClassicalSixthBranch.r = (103653312891857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2528
  · change upperPayment 2529 ≤ upperValue ((point split endpoint 4096 2529+point split endpoint 4096 2530)/2)
    have hp : upperPayment 2529 = (218053047919:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2529+point split endpoint 4096 2530)/2 = (639768477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639768477:ℝ)/168755200)*ClassicalSixthBranch.v ((639768477:ℝ)/168755200)/ClassicalSixthBranch.r = (103632414453081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2529
  · change upperPayment 2530 ≤ upperValue ((point split endpoint 4096 2530+point split endpoint 4096 2531)/2)
    have hp : upperPayment 2530 = (217939854462:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2530+point split endpoint 4096 2531)/2 = (639793627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639793627:ℝ)/168755200)*ClassicalSixthBranch.v ((639793627:ℝ)/168755200)/ClassicalSixthBranch.r = (103611518038377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2530
  · change upperPayment 2531 ≤ upperValue ((point split endpoint 4096 2531+point split endpoint 4096 2532)/2)
    have hp : upperPayment 2531 = (217826631726:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2531+point split endpoint 4096 2532)/2 = (639818777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639818777:ℝ)/168755200)*ClassicalSixthBranch.v ((639818777:ℝ)/168755200)/ClassicalSixthBranch.r = (103590623647745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2531
  · change upperPayment 2532 ≤ upperValue ((point split endpoint 4096 2532+point split endpoint 4096 2533)/2)
    have hp : upperPayment 2532 = (217713379706:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2532+point split endpoint 4096 2533)/2 = (639843927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639843927:ℝ)/168755200)*ClassicalSixthBranch.v ((639843927:ℝ)/168755200)/ClassicalSixthBranch.r = (103569731281185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2532
  · change upperPayment 2533 ≤ upperValue ((point split endpoint 4096 2533+point split endpoint 4096 2534)/2)
    have hp : upperPayment 2533 = (217600098395:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2533+point split endpoint 4096 2534)/2 = (639869077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639869077:ℝ)/168755200)*ClassicalSixthBranch.v ((639869077:ℝ)/168755200)/ClassicalSixthBranch.r = (103548840938697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2533
  · change upperPayment 2534 ≤ upperValue ((point split endpoint 4096 2534+point split endpoint 4096 2535)/2)
    have hp : upperPayment 2534 = (217486787787:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2534+point split endpoint 4096 2535)/2 = (639894227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639894227:ℝ)/168755200)*ClassicalSixthBranch.v ((639894227:ℝ)/168755200)/ClassicalSixthBranch.r = (103527952620281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2534
  · change upperPayment 2535 ≤ upperValue ((point split endpoint 4096 2535+point split endpoint 4096 2536)/2)
    have hp : upperPayment 2535 = (217373447876:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2535+point split endpoint 4096 2536)/2 = (639919377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639919377:ℝ)/168755200)*ClassicalSixthBranch.v ((639919377:ℝ)/168755200)/ClassicalSixthBranch.r = (103507066325937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2535
  · change upperPayment 2536 ≤ upperValue ((point split endpoint 4096 2536+point split endpoint 4096 2537)/2)
    have hp : upperPayment 2536 = (217260078654:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2536+point split endpoint 4096 2537)/2 = (639944527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639944527:ℝ)/168755200)*ClassicalSixthBranch.v ((639944527:ℝ)/168755200)/ClassicalSixthBranch.r = (103486182055665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2536
  · change upperPayment 2537 ≤ upperValue ((point split endpoint 4096 2537+point split endpoint 4096 2538)/2)
    have hp : upperPayment 2537 = (217146680117:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2537+point split endpoint 4096 2538)/2 = (639969677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639969677:ℝ)/168755200)*ClassicalSixthBranch.v ((639969677:ℝ)/168755200)/ClassicalSixthBranch.r = (103465299809465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2537
  · change upperPayment 2538 ≤ upperValue ((point split endpoint 4096 2538+point split endpoint 4096 2539)/2)
    have hp : upperPayment 2538 = (217033252256:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2538+point split endpoint 4096 2539)/2 = (639994827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((639994827:ℝ)/168755200)*ClassicalSixthBranch.v ((639994827:ℝ)/168755200)/ClassicalSixthBranch.r = (103444419587337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2538
  · change upperPayment 2539 ≤ upperValue ((point split endpoint 4096 2539+point split endpoint 4096 2540)/2)
    have hp : upperPayment 2539 = (216919795067:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2539+point split endpoint 4096 2540)/2 = (640019977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640019977:ℝ)/168755200)*ClassicalSixthBranch.v ((640019977:ℝ)/168755200)/ClassicalSixthBranch.r = (103423541389281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2539
  · change upperPayment 2540 ≤ upperValue ((point split endpoint 4096 2540+point split endpoint 4096 2541)/2)
    have hp : upperPayment 2540 = (216806308541:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2540+point split endpoint 4096 2541)/2 = (640045127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640045127:ℝ)/168755200)*ClassicalSixthBranch.v ((640045127:ℝ)/168755200)/ClassicalSixthBranch.r = (103402665215297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2540
  · change upperPayment 2541 ≤ upperValue ((point split endpoint 4096 2541+point split endpoint 4096 2542)/2)
    have hp : upperPayment 2541 = (216692792674:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2541+point split endpoint 4096 2542)/2 = (640070277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640070277:ℝ)/168755200)*ClassicalSixthBranch.v ((640070277:ℝ)/168755200)/ClassicalSixthBranch.r = (103381791065385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2541
  · change upperPayment 2542 ≤ upperValue ((point split endpoint 4096 2542+point split endpoint 4096 2543)/2)
    have hp : upperPayment 2542 = (216579247458:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2542+point split endpoint 4096 2543)/2 = (640095427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640095427:ℝ)/168755200)*ClassicalSixthBranch.v ((640095427:ℝ)/168755200)/ClassicalSixthBranch.r = (103360918939545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2542
  · change upperPayment 2543 ≤ upperValue ((point split endpoint 4096 2543+point split endpoint 4096 2544)/2)
    have hp : upperPayment 2543 = (216465672887:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2543+point split endpoint 4096 2544)/2 = (640120577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((640120577:ℝ)/168755200)*ClassicalSixthBranch.v ((640120577:ℝ)/168755200)/ClassicalSixthBranch.r = (103340048837777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2543
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_158
