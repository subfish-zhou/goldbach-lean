import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints105
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_105 (j : Fin 16) : lowerPayment (16*105+j.val) ≤
    lowerValue ((point 2 split 4096 (16*105+j.val)+point 2 split 4096 (16*105+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1680 ≤ lowerValue ((point 2 split 4096 1680+point 2 split 4096 1681)/2)
    have hp : lowerPayment 1680 = (202953593392:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1680+point 2 split 4096 1681)/2 = (435419691:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435419691:ℝ)/168755200)/ClassicalSixthBranch.v ((435419691:ℝ)/168755200) = (684089547547:ℝ)/339901203864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1680
  · change lowerPayment 1681 ≤ lowerValue ((point 2 split 4096 1681+point 2 split 4096 1682)/2)
    have hp : lowerPayment 1681 = (203048812839:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1681+point 2 split 4096 1682)/2 = (435477953:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435477953:ℝ)/168755200)/ClassicalSixthBranch.v ((435477953:ℝ)/168755200) = (684012233873:ℝ)/339853195976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1681
  · change lowerPayment 1682 ≤ lowerValue ((point 2 split 4096 1682+point 2 split 4096 1683)/2)
    have hp : lowerPayment 1682 = (203144016392:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1682+point 2 split 4096 1683)/2 = (87107243:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87107243:ℝ)/33751040)/ClassicalSixthBranch.v ((87107243:ℝ)/33751040) = (683934920199:ℝ)/339805188088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1682
  · change lowerPayment 1683 ≤ lowerValue ((point 2 split 4096 1683+point 2 split 4096 1684)/2)
    have hp : lowerPayment 1683 = (203239204069:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1683+point 2 split 4096 1684)/2 = (435594477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435594477:ℝ)/168755200)/ClassicalSixthBranch.v ((435594477:ℝ)/168755200) = (27354304261:ℝ)/13590287208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1683
  · change lowerPayment 1684 ≤ lowerValue ((point 2 split 4096 1684+point 2 split 4096 1685)/2)
    have hp : lowerPayment 1684 = (203334375891:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1684+point 2 split 4096 1685)/2 = (435652739:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435652739:ℝ)/168755200)/ClassicalSixthBranch.v ((435652739:ℝ)/168755200) = (683780292851:ℝ)/339709172312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1684
  · change lowerPayment 1685 ≤ lowerValue ((point 2 split 4096 1685+point 2 split 4096 1686)/2)
    have hp : lowerPayment 1685 = (203429531876:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1685+point 2 split 4096 1686)/2 = (435711001:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435711001:ℝ)/168755200)/ClassicalSixthBranch.v ((435711001:ℝ)/168755200) = (683702979177:ℝ)/339661164424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1685
  · change lowerPayment 1686 ≤ lowerValue ((point 2 split 4096 1686+point 2 split 4096 1687)/2)
    have hp : lowerPayment 1686 = (203524672043:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1686+point 2 split 4096 1687)/2 = (435769263:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435769263:ℝ)/168755200)/ClassicalSixthBranch.v ((435769263:ℝ)/168755200) = (683625665503:ℝ)/339613156536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1686
  · change lowerPayment 1687 ≤ lowerValue ((point 2 split 4096 1687+point 2 split 4096 1688)/2)
    have hp : lowerPayment 1687 = (203619796412:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1687+point 2 split 4096 1688)/2 = (17433101:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17433101:ℝ)/6750208)/ClassicalSixthBranch.v ((17433101:ℝ)/6750208) = (683548351829:ℝ)/339565148648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1687
  · change lowerPayment 1688 ≤ lowerValue ((point 2 split 4096 1688+point 2 split 4096 1689)/2)
    have hp : lowerPayment 1688 = (203714905002:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1688+point 2 split 4096 1689)/2 = (435885787:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435885787:ℝ)/168755200)/ClassicalSixthBranch.v ((435885787:ℝ)/168755200) = (136694207631:ℝ)/67903428152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1688
  · change lowerPayment 1689 ≤ lowerValue ((point 2 split 4096 1689+point 2 split 4096 1690)/2)
    have hp : lowerPayment 1689 = (203809997832:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1689+point 2 split 4096 1690)/2 = (435944049:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((435944049:ℝ)/168755200)/ClassicalSixthBranch.v ((435944049:ℝ)/168755200) = (683393724481:ℝ)/339469132872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1689
  · change lowerPayment 1690 ≤ lowerValue ((point 2 split 4096 1690+point 2 split 4096 1691)/2)
    have hp : lowerPayment 1690 = (203905074922:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1690+point 2 split 4096 1691)/2 = (436002311:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436002311:ℝ)/168755200)/ClassicalSixthBranch.v ((436002311:ℝ)/168755200) = (683316410807:ℝ)/339421124984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1690
  · change lowerPayment 1691 ≤ lowerValue ((point 2 split 4096 1691+point 2 split 4096 1692)/2)
    have hp : lowerPayment 1691 = (204000136290:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1691+point 2 split 4096 1692)/2 = (436060573:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436060573:ℝ)/168755200)/ClassicalSixthBranch.v ((436060573:ℝ)/168755200) = (683239097133:ℝ)/339373117096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1691
  · change lowerPayment 1692 ≤ lowerValue ((point 2 split 4096 1692+point 2 split 4096 1693)/2)
    have hp : lowerPayment 1692 = (204095181956:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1692+point 2 split 4096 1693)/2 = (87223767:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87223767:ℝ)/33751040)/ClassicalSixthBranch.v ((87223767:ℝ)/33751040) = (683161783459:ℝ)/339325109208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1692
  · change lowerPayment 1693 ≤ lowerValue ((point 2 split 4096 1693+point 2 split 4096 1694)/2)
    have hp : lowerPayment 1693 = (204190211939:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1693+point 2 split 4096 1694)/2 = (436177097:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436177097:ℝ)/168755200)/ClassicalSixthBranch.v ((436177097:ℝ)/168755200) = (136616893957:ℝ)/67855420264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1693
  · change lowerPayment 1694 ≤ lowerValue ((point 2 split 4096 1694+point 2 split 4096 1695)/2)
    have hp : lowerPayment 1694 = (204285226258:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1694+point 2 split 4096 1695)/2 = (436235359:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436235359:ℝ)/168755200)/ClassicalSixthBranch.v ((436235359:ℝ)/168755200) = (683007156111:ℝ)/339229093432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1694
  · change lowerPayment 1695 ≤ lowerValue ((point 2 split 4096 1695+point 2 split 4096 1696)/2)
    have hp : lowerPayment 1695 = (204380224933:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1695+point 2 split 4096 1696)/2 = (436293621:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436293621:ℝ)/168755200)/ClassicalSixthBranch.v ((436293621:ℝ)/168755200) = (682929842437:ℝ)/339181085544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1695
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_105
