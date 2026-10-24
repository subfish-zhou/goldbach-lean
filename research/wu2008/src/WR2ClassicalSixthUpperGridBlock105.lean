import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints105
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_105 (j : Fin 16) : upperPayment (16*105+j.val) ≤
    upperValue ((point split endpoint 4096 (16*105+j.val)+point split endpoint 4096 (16*105+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1680 ≤ upperValue ((point split endpoint 4096 1680+point split endpoint 4096 1681)/2)
    have hp : upperPayment 1680 = (304193230244:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1680+point split endpoint 4096 1681)/2 = (618416127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618416127:ℝ)/168755200)*ClassicalSixthBranch.v ((618416127:ℝ)/168755200)/ClassicalSixthBranch.r = (122103806316177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1680
  · change upperPayment 1681 ≤ upperValue ((point split endpoint 4096 1681+point split endpoint 4096 1682)/2)
    have hp : upperPayment 1681 = (304102824959:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1681+point split endpoint 4096 1682)/2 = (618441277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618441277:ℝ)/168755200)*ClassicalSixthBranch.v ((618441277:ℝ)/168755200)/ClassicalSixthBranch.r = (122081191464345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1681
  · change upperPayment 1682 ≤ upperValue ((point split endpoint 4096 1682+point split endpoint 4096 1683)/2)
    have hp : upperPayment 1682 = (304012395003:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1682+point split endpoint 4096 1683)/2 = (618466427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618466427:ℝ)/168755200)*ClassicalSixthBranch.v ((618466427:ℝ)/168755200)/ClassicalSixthBranch.r = (122058578636585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1682
  · change upperPayment 1683 ≤ upperValue ((point split endpoint 4096 1683+point split endpoint 4096 1684)/2)
    have hp : upperPayment 1683 = (303921940370:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1683+point split endpoint 4096 1684)/2 = (618491577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618491577:ℝ)/168755200)*ClassicalSixthBranch.v ((618491577:ℝ)/168755200)/ClassicalSixthBranch.r = (122035967832897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1683
  · change upperPayment 1684 ≤ upperValue ((point split endpoint 4096 1684+point split endpoint 4096 1685)/2)
    have hp : upperPayment 1684 = (303831461055:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1684+point split endpoint 4096 1685)/2 = (618516727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618516727:ℝ)/168755200)*ClassicalSixthBranch.v ((618516727:ℝ)/168755200)/ClassicalSixthBranch.r = (122013359053281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1684
  · change upperPayment 1685 ≤ upperValue ((point split endpoint 4096 1685+point split endpoint 4096 1686)/2)
    have hp : upperPayment 1685 = (303740957055:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1685+point split endpoint 4096 1686)/2 = (618541877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618541877:ℝ)/168755200)*ClassicalSixthBranch.v ((618541877:ℝ)/168755200)/ClassicalSixthBranch.r = (121990752297737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1685
  · change upperPayment 1686 ≤ upperValue ((point split endpoint 4096 1686+point split endpoint 4096 1687)/2)
    have hp : upperPayment 1686 = (303650428364:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1686+point split endpoint 4096 1687)/2 = (618567027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618567027:ℝ)/168755200)*ClassicalSixthBranch.v ((618567027:ℝ)/168755200)/ClassicalSixthBranch.r = (121968147566265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1686
  · change upperPayment 1687 ≤ upperValue ((point split endpoint 4096 1687+point split endpoint 4096 1688)/2)
    have hp : upperPayment 1687 = (303559874979:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1687+point split endpoint 4096 1688)/2 = (618592177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618592177:ℝ)/168755200)*ClassicalSixthBranch.v ((618592177:ℝ)/168755200)/ClassicalSixthBranch.r = (121945544858865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1687
  · change upperPayment 1688 ≤ upperValue ((point split endpoint 4096 1688+point split endpoint 4096 1689)/2)
    have hp : upperPayment 1688 = (303469296894:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1688+point split endpoint 4096 1689)/2 = (618617327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618617327:ℝ)/168755200)*ClassicalSixthBranch.v ((618617327:ℝ)/168755200)/ClassicalSixthBranch.r = (121922944175537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1688
  · change upperPayment 1689 ≤ upperValue ((point split endpoint 4096 1689+point split endpoint 4096 1690)/2)
    have hp : upperPayment 1689 = (303378694105:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1689+point split endpoint 4096 1690)/2 = (618642477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618642477:ℝ)/168755200)*ClassicalSixthBranch.v ((618642477:ℝ)/168755200)/ClassicalSixthBranch.r = (121900345516281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1689
  · change upperPayment 1690 ≤ upperValue ((point split endpoint 4096 1690+point split endpoint 4096 1691)/2)
    have hp : upperPayment 1690 = (303288066608:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1690+point split endpoint 4096 1691)/2 = (618667627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618667627:ℝ)/168755200)*ClassicalSixthBranch.v ((618667627:ℝ)/168755200)/ClassicalSixthBranch.r = (121877748881097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1690
  · change upperPayment 1691 ≤ upperValue ((point split endpoint 4096 1691+point split endpoint 4096 1692)/2)
    have hp : upperPayment 1691 = (303197414398:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1691+point split endpoint 4096 1692)/2 = (618692777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618692777:ℝ)/168755200)*ClassicalSixthBranch.v ((618692777:ℝ)/168755200)/ClassicalSixthBranch.r = (121855154269985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1691
  · change upperPayment 1692 ≤ upperValue ((point split endpoint 4096 1692+point split endpoint 4096 1693)/2)
    have hp : upperPayment 1692 = (303106737469:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1692+point split endpoint 4096 1693)/2 = (618717927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618717927:ℝ)/168755200)*ClassicalSixthBranch.v ((618717927:ℝ)/168755200)/ClassicalSixthBranch.r = (121832561682945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1692
  · change upperPayment 1693 ≤ upperValue ((point split endpoint 4096 1693+point split endpoint 4096 1694)/2)
    have hp : upperPayment 1693 = (303016035819:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1693+point split endpoint 4096 1694)/2 = (618743077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618743077:ℝ)/168755200)*ClassicalSixthBranch.v ((618743077:ℝ)/168755200)/ClassicalSixthBranch.r = (121809971119977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1693
  · change upperPayment 1694 ≤ upperValue ((point split endpoint 4096 1694+point split endpoint 4096 1695)/2)
    have hp : upperPayment 1694 = (302925309442:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1694+point split endpoint 4096 1695)/2 = (618768227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618768227:ℝ)/168755200)*ClassicalSixthBranch.v ((618768227:ℝ)/168755200)/ClassicalSixthBranch.r = (121787382581081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1694
  · change upperPayment 1695 ≤ upperValue ((point split endpoint 4096 1695+point split endpoint 4096 1696)/2)
    have hp : upperPayment 1695 = (302834558334:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1695+point split endpoint 4096 1696)/2 = (618793377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((618793377:ℝ)/168755200)*ClassicalSixthBranch.v ((618793377:ℝ)/168755200)/ClassicalSixthBranch.r = (121764796066257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1695
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_105
