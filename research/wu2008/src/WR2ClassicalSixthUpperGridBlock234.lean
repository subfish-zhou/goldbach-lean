import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints234
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_234 (j : Fin 16) : upperPayment (16*234+j.val) ≤
    upperValue ((point split endpoint 4096 (16*234+j.val)+point split endpoint 4096 (16*234+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3744 ≤ upperValue ((point split endpoint 4096 3744+point split endpoint 4096 3745)/2)
    have hp : upperPayment 3744 = (56761913064:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3744+point split endpoint 4096 3745)/2 = (670325727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670325727:ℝ)/168755200)*ClassicalSixthBranch.v ((670325727:ℝ)/168755200)/ClassicalSixthBranch.r = (79736033808081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3744
  · change upperPayment 3745 ≤ upperValue ((point split endpoint 4096 3745+point split endpoint 4096 3746)/2)
    have hp : upperPayment 3745 = (56607545466:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3745+point split endpoint 4096 3746)/2 = (670350877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670350877:ℝ)/168755200)*ClassicalSixthBranch.v ((670350877:ℝ)/168755200)/ClassicalSixthBranch.r = (79717596640857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3745
  · change upperPayment 3746 ≤ upperValue ((point split endpoint 4096 3746+point split endpoint 4096 3747)/2)
    have hp : upperPayment 3746 = (56453138531:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3746+point split endpoint 4096 3747)/2 = (670376027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670376027:ℝ)/168755200)*ClassicalSixthBranch.v ((670376027:ℝ)/168755200)/ClassicalSixthBranch.r = (79699161497705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3746
  · change upperPayment 3747 ≤ upperValue ((point split endpoint 4096 3747+point split endpoint 4096 3748)/2)
    have hp : upperPayment 3747 = (56298692247:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3747+point split endpoint 4096 3748)/2 = (670401177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670401177:ℝ)/168755200)*ClassicalSixthBranch.v ((670401177:ℝ)/168755200)/ClassicalSixthBranch.r = (79680728378625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3747
  · change upperPayment 3748 ≤ upperValue ((point split endpoint 4096 3748+point split endpoint 4096 3749)/2)
    have hp : upperPayment 3748 = (56144206605:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3748+point split endpoint 4096 3749)/2 = (670426327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670426327:ℝ)/168755200)*ClassicalSixthBranch.v ((670426327:ℝ)/168755200)/ClassicalSixthBranch.r = (79662297283617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3748
  · change upperPayment 3749 ≤ upperValue ((point split endpoint 4096 3749+point split endpoint 4096 3750)/2)
    have hp : upperPayment 3749 = (55989681594:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3749+point split endpoint 4096 3750)/2 = (670451477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670451477:ℝ)/168755200)*ClassicalSixthBranch.v ((670451477:ℝ)/168755200)/ClassicalSixthBranch.r = (79643868212681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3749
  · change upperPayment 3750 ≤ upperValue ((point split endpoint 4096 3750+point split endpoint 4096 3751)/2)
    have hp : upperPayment 3750 = (55835117204:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3750+point split endpoint 4096 3751)/2 = (670476627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670476627:ℝ)/168755200)*ClassicalSixthBranch.v ((670476627:ℝ)/168755200)/ClassicalSixthBranch.r = (79625441165817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3750
  · change upperPayment 3751 ≤ upperValue ((point split endpoint 4096 3751+point split endpoint 4096 3752)/2)
    have hp : upperPayment 3751 = (55680513423:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3751+point split endpoint 4096 3752)/2 = (670501777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670501777:ℝ)/168755200)*ClassicalSixthBranch.v ((670501777:ℝ)/168755200)/ClassicalSixthBranch.r = (79607016143025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3751
  · change upperPayment 3752 ≤ upperValue ((point split endpoint 4096 3752+point split endpoint 4096 3753)/2)
    have hp : upperPayment 3752 = (55525870242:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3752+point split endpoint 4096 3753)/2 = (670526927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670526927:ℝ)/168755200)*ClassicalSixthBranch.v ((670526927:ℝ)/168755200)/ClassicalSixthBranch.r = (79588593144305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3752
  · change upperPayment 3753 ≤ upperValue ((point split endpoint 4096 3753+point split endpoint 4096 3754)/2)
    have hp : upperPayment 3753 = (55371187649:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3753+point split endpoint 4096 3754)/2 = (670552077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670552077:ℝ)/168755200)*ClassicalSixthBranch.v ((670552077:ℝ)/168755200)/ClassicalSixthBranch.r = (79570172169657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3753
  · change upperPayment 3754 ≤ upperValue ((point split endpoint 4096 3754+point split endpoint 4096 3755)/2)
    have hp : upperPayment 3754 = (55216465635:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3754+point split endpoint 4096 3755)/2 = (670577227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670577227:ℝ)/168755200)*ClassicalSixthBranch.v ((670577227:ℝ)/168755200)/ClassicalSixthBranch.r = (79551753219081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3754
  · change upperPayment 3755 ≤ upperValue ((point split endpoint 4096 3755+point split endpoint 4096 3756)/2)
    have hp : upperPayment 3755 = (55061704188:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3755+point split endpoint 4096 3756)/2 = (670602377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670602377:ℝ)/168755200)*ClassicalSixthBranch.v ((670602377:ℝ)/168755200)/ClassicalSixthBranch.r = (79533336292577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3755
  · change upperPayment 3756 ≤ upperValue ((point split endpoint 4096 3756+point split endpoint 4096 3757)/2)
    have hp : upperPayment 3756 = (54906903298:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3756+point split endpoint 4096 3757)/2 = (670627527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670627527:ℝ)/168755200)*ClassicalSixthBranch.v ((670627527:ℝ)/168755200)/ClassicalSixthBranch.r = (79514921390145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3756
  · change upperPayment 3757 ≤ upperValue ((point split endpoint 4096 3757+point split endpoint 4096 3758)/2)
    have hp : upperPayment 3757 = (54752062955:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3757+point split endpoint 4096 3758)/2 = (670652677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670652677:ℝ)/168755200)*ClassicalSixthBranch.v ((670652677:ℝ)/168755200)/ClassicalSixthBranch.r = (79496508511785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3757
  · change upperPayment 3758 ≤ upperValue ((point split endpoint 4096 3758+point split endpoint 4096 3759)/2)
    have hp : upperPayment 3758 = (54597183148:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3758+point split endpoint 4096 3759)/2 = (670677827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670677827:ℝ)/168755200)*ClassicalSixthBranch.v ((670677827:ℝ)/168755200)/ClassicalSixthBranch.r = (79478097657497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3758
  · change upperPayment 3759 ≤ upperValue ((point split endpoint 4096 3759+point split endpoint 4096 3760)/2)
    have hp : upperPayment 3759 = (54442263866:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3759+point split endpoint 4096 3760)/2 = (670702977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((670702977:ℝ)/168755200)*ClassicalSixthBranch.v ((670702977:ℝ)/168755200)/ClassicalSixthBranch.r = (79459688827281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3759
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_234
