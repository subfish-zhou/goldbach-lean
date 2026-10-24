import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints230
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_230 (j : Fin 16) : upperPayment (16*230+j.val) ≤
    upperValue ((point split endpoint 4096 (16*230+j.val)+point split endpoint 4096 (16*230+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3680 ≤ upperValue ((point split endpoint 4096 3680+point split endpoint 4096 3681)/2)
    have hp : upperPayment 3680 = (66560096302:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3680+point split endpoint 4096 3681)/2 = (668716127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668716127:ℝ)/168755200)*ClassicalSixthBranch.v ((668716127:ℝ)/168755200)/ClassicalSixthBranch.r = (80920222580177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3680
  · change upperPayment 3681 ≤ upperValue ((point split endpoint 4096 3681+point split endpoint 4096 3682)/2)
    have hp : upperPayment 3681 = (66408224585:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3681+point split endpoint 4096 3682)/2 = (668741277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668741277:ℝ)/168755200)*ClassicalSixthBranch.v ((668741277:ℝ)/168755200)/ClassicalSixthBranch.r = (80901655872345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3681
  · change upperPayment 3682 ≤ upperValue ((point split endpoint 4096 3682+point split endpoint 4096 3683)/2)
    have hp : upperPayment 3682 = (66256314195:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3682+point split endpoint 4096 3683)/2 = (668766427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668766427:ℝ)/168755200)*ClassicalSixthBranch.v ((668766427:ℝ)/168755200)/ClassicalSixthBranch.r = (80883091188585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3682
  · change upperPayment 3683 ≤ upperValue ((point split endpoint 4096 3683+point split endpoint 4096 3684)/2)
    have hp : upperPayment 3683 = (66104365123:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3683+point split endpoint 4096 3684)/2 = (668791577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668791577:ℝ)/168755200)*ClassicalSixthBranch.v ((668791577:ℝ)/168755200)/ClassicalSixthBranch.r = (80864528528897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3683
  · change upperPayment 3684 ≤ upperValue ((point split endpoint 4096 3684+point split endpoint 4096 3685)/2)
    have hp : upperPayment 3684 = (65952377357:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3684+point split endpoint 4096 3685)/2 = (668816727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668816727:ℝ)/168755200)*ClassicalSixthBranch.v ((668816727:ℝ)/168755200)/ClassicalSixthBranch.r = (80845967893281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3684
  · change upperPayment 3685 ≤ upperValue ((point split endpoint 4096 3685+point split endpoint 4096 3686)/2)
    have hp : upperPayment 3685 = (65800350889:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3685+point split endpoint 4096 3686)/2 = (668841877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668841877:ℝ)/168755200)*ClassicalSixthBranch.v ((668841877:ℝ)/168755200)/ClassicalSixthBranch.r = (80827409281737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3685
  · change upperPayment 3686 ≤ upperValue ((point split endpoint 4096 3686+point split endpoint 4096 3687)/2)
    have hp : upperPayment 3686 = (65648285708:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3686+point split endpoint 4096 3687)/2 = (668867027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668867027:ℝ)/168755200)*ClassicalSixthBranch.v ((668867027:ℝ)/168755200)/ClassicalSixthBranch.r = (80808852694265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3686
  · change upperPayment 3687 ≤ upperValue ((point split endpoint 4096 3687+point split endpoint 4096 3688)/2)
    have hp : upperPayment 3687 = (65496181803:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3687+point split endpoint 4096 3688)/2 = (668892177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668892177:ℝ)/168755200)*ClassicalSixthBranch.v ((668892177:ℝ)/168755200)/ClassicalSixthBranch.r = (80790298130865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3687
  · change upperPayment 3688 ≤ upperValue ((point split endpoint 4096 3688+point split endpoint 4096 3689)/2)
    have hp : upperPayment 3688 = (65344039164:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3688+point split endpoint 4096 3689)/2 = (668917327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668917327:ℝ)/168755200)*ClassicalSixthBranch.v ((668917327:ℝ)/168755200)/ClassicalSixthBranch.r = (80771745591537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3688
  · change upperPayment 3689 ≤ upperValue ((point split endpoint 4096 3689+point split endpoint 4096 3690)/2)
    have hp : upperPayment 3689 = (65191857781:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3689+point split endpoint 4096 3690)/2 = (668942477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668942477:ℝ)/168755200)*ClassicalSixthBranch.v ((668942477:ℝ)/168755200)/ClassicalSixthBranch.r = (80753195076281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3689
  · change upperPayment 3690 ≤ upperValue ((point split endpoint 4096 3690+point split endpoint 4096 3691)/2)
    have hp : upperPayment 3690 = (65039637643:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3690+point split endpoint 4096 3691)/2 = (668967627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668967627:ℝ)/168755200)*ClassicalSixthBranch.v ((668967627:ℝ)/168755200)/ClassicalSixthBranch.r = (80734646585097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3690
  · change upperPayment 3691 ≤ upperValue ((point split endpoint 4096 3691+point split endpoint 4096 3692)/2)
    have hp : upperPayment 3691 = (64887378741:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3691+point split endpoint 4096 3692)/2 = (668992777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((668992777:ℝ)/168755200)*ClassicalSixthBranch.v ((668992777:ℝ)/168755200)/ClassicalSixthBranch.r = (80716100117985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3691
  · change upperPayment 3692 ≤ upperValue ((point split endpoint 4096 3692+point split endpoint 4096 3693)/2)
    have hp : upperPayment 3692 = (64735081064:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3692+point split endpoint 4096 3693)/2 = (669017927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669017927:ℝ)/168755200)*ClassicalSixthBranch.v ((669017927:ℝ)/168755200)/ClassicalSixthBranch.r = (80697555674945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3692
  · change upperPayment 3693 ≤ upperValue ((point split endpoint 4096 3693+point split endpoint 4096 3694)/2)
    have hp : upperPayment 3693 = (64582744601:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3693+point split endpoint 4096 3694)/2 = (669043077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669043077:ℝ)/168755200)*ClassicalSixthBranch.v ((669043077:ℝ)/168755200)/ClassicalSixthBranch.r = (80679013255977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3693
  · change upperPayment 3694 ≤ upperValue ((point split endpoint 4096 3694+point split endpoint 4096 3695)/2)
    have hp : upperPayment 3694 = (64430369343:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3694+point split endpoint 4096 3695)/2 = (669068227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669068227:ℝ)/168755200)*ClassicalSixthBranch.v ((669068227:ℝ)/168755200)/ClassicalSixthBranch.r = (80660472861081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3694
  · change upperPayment 3695 ≤ upperValue ((point split endpoint 4096 3695+point split endpoint 4096 3696)/2)
    have hp : upperPayment 3695 = (64277955279:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3695+point split endpoint 4096 3696)/2 = (669093377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669093377:ℝ)/168755200)*ClassicalSixthBranch.v ((669093377:ℝ)/168755200)/ClassicalSixthBranch.r = (80641934490257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3695
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_230
