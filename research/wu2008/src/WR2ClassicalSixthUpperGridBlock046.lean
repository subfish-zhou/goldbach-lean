import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints046
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_046 (j : Fin 16) : upperPayment (16*46+j.val) ≤
    upperValue ((point split endpoint 4096 (16*46+j.val)+point split endpoint 4096 (16*46+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 736 ≤ upperValue ((point split endpoint 4096 736+point split endpoint 4096 737)/2)
    have hp : upperPayment 736 = (379112372762:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 736+point split endpoint 4096 737)/2 = (594674527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594674527:ℝ)/168755200)*ClassicalSixthBranch.v ((594674527:ℝ)/168755200)/ClassicalSixthBranch.r = (144355043520465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_736
  · change upperPayment 737 ≤ upperValue ((point split endpoint 4096 737+point split endpoint 4096 738)/2)
    have hp : upperPayment 737 = (379043472170:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 737+point split endpoint 4096 738)/2 = (594699677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594699677:ℝ)/168755200)*ClassicalSixthBranch.v ((594699677:ℝ)/168755200)/ClassicalSixthBranch.r = (144330517944665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_737
  · change upperPayment 738 ≤ upperValue ((point split endpoint 4096 738+point split endpoint 4096 739)/2)
    have hp : upperPayment 738 = (378974550448:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 738+point split endpoint 4096 739)/2 = (594724827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594724827:ℝ)/168755200)*ClassicalSixthBranch.v ((594724827:ℝ)/168755200)/ClassicalSixthBranch.r = (144305994392937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_738
  · change upperPayment 739 ≤ upperValue ((point split endpoint 4096 739+point split endpoint 4096 740)/2)
    have hp : upperPayment 739 = (378905607593:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 739+point split endpoint 4096 740)/2 = (594749977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594749977:ℝ)/168755200)*ClassicalSixthBranch.v ((594749977:ℝ)/168755200)/ClassicalSixthBranch.r = (144281472865281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_739
  · change upperPayment 740 ≤ upperValue ((point split endpoint 4096 740+point split endpoint 4096 741)/2)
    have hp : upperPayment 740 = (378836643602:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 740+point split endpoint 4096 741)/2 = (594775127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594775127:ℝ)/168755200)*ClassicalSixthBranch.v ((594775127:ℝ)/168755200)/ClassicalSixthBranch.r = (144256953361697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_740
  · change upperPayment 741 ≤ upperValue ((point split endpoint 4096 741+point split endpoint 4096 742)/2)
    have hp : upperPayment 741 = (378767658473:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 741+point split endpoint 4096 742)/2 = (594800277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594800277:ℝ)/168755200)*ClassicalSixthBranch.v ((594800277:ℝ)/168755200)/ClassicalSixthBranch.r = (144232435882185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_741
  · change upperPayment 742 ≤ upperValue ((point split endpoint 4096 742+point split endpoint 4096 743)/2)
    have hp : upperPayment 742 = (378698652201:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 742+point split endpoint 4096 743)/2 = (594825427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594825427:ℝ)/168755200)*ClassicalSixthBranch.v ((594825427:ℝ)/168755200)/ClassicalSixthBranch.r = (144207920426745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_742
  · change upperPayment 743 ≤ upperValue ((point split endpoint 4096 743+point split endpoint 4096 744)/2)
    have hp : upperPayment 743 = (378629624785:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 743+point split endpoint 4096 744)/2 = (594850577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594850577:ℝ)/168755200)*ClassicalSixthBranch.v ((594850577:ℝ)/168755200)/ClassicalSixthBranch.r = (144183406995377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_743
  · change upperPayment 744 ≤ upperValue ((point split endpoint 4096 744+point split endpoint 4096 745)/2)
    have hp : upperPayment 744 = (378560576220:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 744+point split endpoint 4096 745)/2 = (594875727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594875727:ℝ)/168755200)*ClassicalSixthBranch.v ((594875727:ℝ)/168755200)/ClassicalSixthBranch.r = (144158895588081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_744
  · change upperPayment 745 ≤ upperValue ((point split endpoint 4096 745+point split endpoint 4096 746)/2)
    have hp : upperPayment 745 = (378491506505:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 745+point split endpoint 4096 746)/2 = (594900877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594900877:ℝ)/168755200)*ClassicalSixthBranch.v ((594900877:ℝ)/168755200)/ClassicalSixthBranch.r = (144134386204857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_745
  · change upperPayment 746 ≤ upperValue ((point split endpoint 4096 746+point split endpoint 4096 747)/2)
    have hp : upperPayment 746 = (378422415635:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 746+point split endpoint 4096 747)/2 = (594926027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594926027:ℝ)/168755200)*ClassicalSixthBranch.v ((594926027:ℝ)/168755200)/ClassicalSixthBranch.r = (144109878845705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_746
  · change upperPayment 747 ≤ upperValue ((point split endpoint 4096 747+point split endpoint 4096 748)/2)
    have hp : upperPayment 747 = (378353303609:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 747+point split endpoint 4096 748)/2 = (594951177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594951177:ℝ)/168755200)*ClassicalSixthBranch.v ((594951177:ℝ)/168755200)/ClassicalSixthBranch.r = (144085373510625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_747
  · change upperPayment 748 ≤ upperValue ((point split endpoint 4096 748+point split endpoint 4096 749)/2)
    have hp : upperPayment 748 = (378284170422:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 748+point split endpoint 4096 749)/2 = (594976327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((594976327:ℝ)/168755200)*ClassicalSixthBranch.v ((594976327:ℝ)/168755200)/ClassicalSixthBranch.r = (1398649225239:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_748
  · change upperPayment 749 ≤ upperValue ((point split endpoint 4096 749+point split endpoint 4096 750)/2)
    have hp : upperPayment 749 = (378215016072:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 749+point split endpoint 4096 750)/2 = (595001477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595001477:ℝ)/168755200)*ClassicalSixthBranch.v ((595001477:ℝ)/168755200)/ClassicalSixthBranch.r = (144036368912681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_749
  · change upperPayment 750 ≤ upperValue ((point split endpoint 4096 750+point split endpoint 4096 751)/2)
    have hp : upperPayment 750 = (378145840555:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 750+point split endpoint 4096 751)/2 = (595026627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595026627:ℝ)/168755200)*ClassicalSixthBranch.v ((595026627:ℝ)/168755200)/ClassicalSixthBranch.r = (144011869649817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_750
  · change upperPayment 751 ≤ upperValue ((point split endpoint 4096 751+point split endpoint 4096 752)/2)
    have hp : upperPayment 751 = (378076643870:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 751+point split endpoint 4096 752)/2 = (595051777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((595051777:ℝ)/168755200)*ClassicalSixthBranch.v ((595051777:ℝ)/168755200)/ClassicalSixthBranch.r = (143987372411025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_751
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_046
