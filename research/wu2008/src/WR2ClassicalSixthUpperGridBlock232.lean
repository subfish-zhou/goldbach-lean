import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints232
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_232 (j : Fin 16) : upperPayment (16*232+j.val) ≤
    upperValue ((point split endpoint 4096 (16*232+j.val)+point split endpoint 4096 (16*232+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3712 ≤ upperValue ((point split endpoint 4096 3712+point split endpoint 4096 3713)/2)
    have hp : upperPayment 3712 = (61680968877:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3712+point split endpoint 4096 3713)/2 = (669520927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669520927:ℝ)/168755200)*ClassicalSixthBranch.v ((669520927:ℝ)/168755200)/ClassicalSixthBranch.r = (80327091869265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3712
  · change upperPayment 3713 ≤ upperValue ((point split endpoint 4096 3713+point split endpoint 4096 3714)/2)
    have hp : upperPayment 3713 = (61527854539:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3713+point split endpoint 4096 3714)/2 = (669546077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669546077:ℝ)/168755200)*ClassicalSixthBranch.v ((669546077:ℝ)/168755200)/ClassicalSixthBranch.r = (80308589931737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3713
  · change upperPayment 3714 ≤ upperValue ((point split endpoint 4096 3714+point split endpoint 4096 3715)/2)
    have hp : upperPayment 3714 = (61374701198:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3714+point split endpoint 4096 3715)/2 = (669571227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669571227:ℝ)/168755200)*ClassicalSixthBranch.v ((669571227:ℝ)/168755200)/ClassicalSixthBranch.r = (80290090018281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3714
  · change upperPayment 3715 ≤ upperValue ((point split endpoint 4096 3715+point split endpoint 4096 3716)/2)
    have hp : upperPayment 3715 = (61221508844:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3715+point split endpoint 4096 3716)/2 = (669596377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669596377:ℝ)/168755200)*ClassicalSixthBranch.v ((669596377:ℝ)/168755200)/ClassicalSixthBranch.r = (80271592128897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3715
  · change upperPayment 3716 ≤ upperValue ((point split endpoint 4096 3716+point split endpoint 4096 3717)/2)
    have hp : upperPayment 3716 = (61068277467:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3716+point split endpoint 4096 3717)/2 = (669621527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669621527:ℝ)/168755200)*ClassicalSixthBranch.v ((669621527:ℝ)/168755200)/ClassicalSixthBranch.r = (80253096263585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3716
  · change upperPayment 3717 ≤ upperValue ((point split endpoint 4096 3717+point split endpoint 4096 3718)/2)
    have hp : upperPayment 3717 = (60915007057:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3717+point split endpoint 4096 3718)/2 = (669646677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669646677:ℝ)/168755200)*ClassicalSixthBranch.v ((669646677:ℝ)/168755200)/ClassicalSixthBranch.r = (80234602422345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3717
  · change upperPayment 3718 ≤ upperValue ((point split endpoint 4096 3718+point split endpoint 4096 3719)/2)
    have hp : upperPayment 3718 = (60761697602:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3718+point split endpoint 4096 3719)/2 = (669671827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669671827:ℝ)/168755200)*ClassicalSixthBranch.v ((669671827:ℝ)/168755200)/ClassicalSixthBranch.r = (80216110605177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3718
  · change upperPayment 3719 ≤ upperValue ((point split endpoint 4096 3719+point split endpoint 4096 3720)/2)
    have hp : upperPayment 3719 = (60608349092:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3719+point split endpoint 4096 3720)/2 = (669696977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669696977:ℝ)/168755200)*ClassicalSixthBranch.v ((669696977:ℝ)/168755200)/ClassicalSixthBranch.r = (80197620812081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3719
  · change upperPayment 3720 ≤ upperValue ((point split endpoint 4096 3720+point split endpoint 4096 3721)/2)
    have hp : upperPayment 3720 = (60454961518:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3720+point split endpoint 4096 3721)/2 = (669722127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669722127:ℝ)/168755200)*ClassicalSixthBranch.v ((669722127:ℝ)/168755200)/ClassicalSixthBranch.r = (80179133043057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3720
  · change upperPayment 3721 ≤ upperValue ((point split endpoint 4096 3721+point split endpoint 4096 3722)/2)
    have hp : upperPayment 3721 = (60301534868:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3721+point split endpoint 4096 3722)/2 = (669747277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669747277:ℝ)/168755200)*ClassicalSixthBranch.v ((669747277:ℝ)/168755200)/ClassicalSixthBranch.r = (80160647298105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3721
  · change upperPayment 3722 ≤ upperValue ((point split endpoint 4096 3722+point split endpoint 4096 3723)/2)
    have hp : upperPayment 3722 = (60148069132:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3722+point split endpoint 4096 3723)/2 = (669772427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669772427:ℝ)/168755200)*ClassicalSixthBranch.v ((669772427:ℝ)/168755200)/ClassicalSixthBranch.r = (80142163577225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3722
  · change upperPayment 3723 ≤ upperValue ((point split endpoint 4096 3723+point split endpoint 4096 3724)/2)
    have hp : upperPayment 3723 = (59994564300:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3723+point split endpoint 4096 3724)/2 = (669797577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669797577:ℝ)/168755200)*ClassicalSixthBranch.v ((669797577:ℝ)/168755200)/ClassicalSixthBranch.r = (80123681880417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3723
  · change upperPayment 3724 ≤ upperValue ((point split endpoint 4096 3724+point split endpoint 4096 3725)/2)
    have hp : upperPayment 3724 = (59841020361:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3724+point split endpoint 4096 3725)/2 = (669822727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669822727:ℝ)/168755200)*ClassicalSixthBranch.v ((669822727:ℝ)/168755200)/ClassicalSixthBranch.r = (80105202207681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3724
  · change upperPayment 3725 ≤ upperValue ((point split endpoint 4096 3725+point split endpoint 4096 3726)/2)
    have hp : upperPayment 3725 = (59687437305:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3725+point split endpoint 4096 3726)/2 = (669847877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669847877:ℝ)/168755200)*ClassicalSixthBranch.v ((669847877:ℝ)/168755200)/ClassicalSixthBranch.r = (80086724559017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3725
  · change upperPayment 3726 ≤ upperValue ((point split endpoint 4096 3726+point split endpoint 4096 3727)/2)
    have hp : upperPayment 3726 = (59533815121:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3726+point split endpoint 4096 3727)/2 = (669873027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669873027:ℝ)/168755200)*ClassicalSixthBranch.v ((669873027:ℝ)/168755200)/ClassicalSixthBranch.r = (80068248934425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3726
  · change upperPayment 3727 ≤ upperValue ((point split endpoint 4096 3727+point split endpoint 4096 3728)/2)
    have hp : upperPayment 3727 = (59380153800:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3727+point split endpoint 4096 3728)/2 = (669898177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((669898177:ℝ)/168755200)*ClassicalSixthBranch.v ((669898177:ℝ)/168755200)/ClassicalSixthBranch.r = (80049775333905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3727
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_232
