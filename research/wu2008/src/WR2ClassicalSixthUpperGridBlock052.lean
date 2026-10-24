import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints052
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_052 (j : Fin 16) : upperPayment (16*52+j.val) ≤
    upperValue ((point split endpoint 4096 (16*52+j.val)+point split endpoint 4096 (16*52+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 832 ≤ upperValue ((point split endpoint 4096 832+point split endpoint 4096 833)/2)
    have hp : upperPayment 832 = (372401125989:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 832+point split endpoint 4096 833)/2 = (597088927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597088927:ℝ)/168755200)*ClassicalSixthBranch.v ((597088927:ℝ)/168755200)/ClassicalSixthBranch.r = (142009818011985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_832
  · change upperPayment 833 ≤ upperValue ((point split endpoint 4096 833+point split endpoint 4096 834)/2)
    have hp : upperPayment 833 = (372330182903:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 833+point split endpoint 4096 834)/2 = (597114077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597114077:ℝ)/168755200)*ClassicalSixthBranch.v ((597114077:ℝ)/168755200)/ClassicalSixthBranch.r = (141985486747097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_833
  · change upperPayment 834 ≤ upperValue ((point split endpoint 4096 834+point split endpoint 4096 835)/2)
    have hp : upperPayment 834 = (372259218390:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 834+point split endpoint 4096 835)/2 = (597139227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597139227:ℝ)/168755200)*ClassicalSixthBranch.v ((597139227:ℝ)/168755200)/ClassicalSixthBranch.r = (141961157506281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_834
  · change upperPayment 835 ≤ upperValue ((point split endpoint 4096 835+point split endpoint 4096 836)/2)
    have hp : upperPayment 835 = (372188232446:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 835+point split endpoint 4096 836)/2 = (597164377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597164377:ℝ)/168755200)*ClassicalSixthBranch.v ((597164377:ℝ)/168755200)/ClassicalSixthBranch.r = (141936830289537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_835
  · change upperPayment 836 ≤ upperValue ((point split endpoint 4096 836+point split endpoint 4096 837)/2)
    have hp : upperPayment 836 = (372117225068:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 836+point split endpoint 4096 837)/2 = (597189527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597189527:ℝ)/168755200)*ClassicalSixthBranch.v ((597189527:ℝ)/168755200)/ClassicalSixthBranch.r = (141912505096865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_836
  · change upperPayment 837 ≤ upperValue ((point split endpoint 4096 837+point split endpoint 4096 838)/2)
    have hp : upperPayment 837 = (372046196254:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 837+point split endpoint 4096 838)/2 = (597214677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597214677:ℝ)/168755200)*ClassicalSixthBranch.v ((597214677:ℝ)/168755200)/ClassicalSixthBranch.r = (141888181928265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_837
  · change upperPayment 838 ≤ upperValue ((point split endpoint 4096 838+point split endpoint 4096 839)/2)
    have hp : upperPayment 838 = (371975145999:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 838+point split endpoint 4096 839)/2 = (597239827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597239827:ℝ)/168755200)*ClassicalSixthBranch.v ((597239827:ℝ)/168755200)/ClassicalSixthBranch.r = (141863860783737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_838
  · change upperPayment 839 ≤ upperValue ((point split endpoint 4096 839+point split endpoint 4096 840)/2)
    have hp : upperPayment 839 = (371904074301:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 839+point split endpoint 4096 840)/2 = (597264977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597264977:ℝ)/168755200)*ClassicalSixthBranch.v ((597264977:ℝ)/168755200)/ClassicalSixthBranch.r = (141839541663281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_839
  · change upperPayment 840 ≤ upperValue ((point split endpoint 4096 840+point split endpoint 4096 841)/2)
    have hp : upperPayment 840 = (371832981157:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 840+point split endpoint 4096 841)/2 = (597290127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597290127:ℝ)/168755200)*ClassicalSixthBranch.v ((597290127:ℝ)/168755200)/ClassicalSixthBranch.r = (141815224566897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_840
  · change upperPayment 841 ≤ upperValue ((point split endpoint 4096 841+point split endpoint 4096 842)/2)
    have hp : upperPayment 841 = (371761866563:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 841+point split endpoint 4096 842)/2 = (597315277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597315277:ℝ)/168755200)*ClassicalSixthBranch.v ((597315277:ℝ)/168755200)/ClassicalSixthBranch.r = (141790909494585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_841
  · change upperPayment 842 ≤ upperValue ((point split endpoint 4096 842+point split endpoint 4096 843)/2)
    have hp : upperPayment 842 = (371690730516:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 842+point split endpoint 4096 843)/2 = (597340427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597340427:ℝ)/168755200)*ClassicalSixthBranch.v ((597340427:ℝ)/168755200)/ClassicalSixthBranch.r = (141766596446345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_842
  · change upperPayment 843 ≤ upperValue ((point split endpoint 4096 843+point split endpoint 4096 844)/2)
    have hp : upperPayment 843 = (371619573013:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 843+point split endpoint 4096 844)/2 = (597365577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597365577:ℝ)/168755200)*ClassicalSixthBranch.v ((597365577:ℝ)/168755200)/ClassicalSixthBranch.r = (141742285422177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_843
  · change upperPayment 844 ≤ upperValue ((point split endpoint 4096 844+point split endpoint 4096 845)/2)
    have hp : upperPayment 844 = (371548394051:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 844+point split endpoint 4096 845)/2 = (597390727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597390727:ℝ)/168755200)*ClassicalSixthBranch.v ((597390727:ℝ)/168755200)/ClassicalSixthBranch.r = (141717976422081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_844
  · change upperPayment 845 ≤ upperValue ((point split endpoint 4096 845+point split endpoint 4096 846)/2)
    have hp : upperPayment 845 = (371477193626:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 845+point split endpoint 4096 846)/2 = (597415877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597415877:ℝ)/168755200)*ClassicalSixthBranch.v ((597415877:ℝ)/168755200)/ClassicalSixthBranch.r = (141693669446057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_845
  · change upperPayment 846 ≤ upperValue ((point split endpoint 4096 846+point split endpoint 4096 847)/2)
    have hp : upperPayment 846 = (371405971736:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 846+point split endpoint 4096 847)/2 = (597441027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597441027:ℝ)/168755200)*ClassicalSixthBranch.v ((597441027:ℝ)/168755200)/ClassicalSixthBranch.r = (141669364494105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_846
  · change upperPayment 847 ≤ upperValue ((point split endpoint 4096 847+point split endpoint 4096 848)/2)
    have hp : upperPayment 847 = (371334728377:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 847+point split endpoint 4096 848)/2 = (597466177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597466177:ℝ)/168755200)*ClassicalSixthBranch.v ((597466177:ℝ)/168755200)/ClassicalSixthBranch.r = (141645061566225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_847
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_052
