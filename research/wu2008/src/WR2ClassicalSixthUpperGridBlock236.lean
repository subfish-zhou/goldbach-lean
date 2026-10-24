import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints236
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_236 (j : Fin 16) : upperPayment (16*236+j.val) ≤
    upperValue ((point split endpoint 4096 (16*236+j.val)+point split endpoint 4096 (16*236+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3776 ≤ upperValue ((point split endpoint 4096 3776+point split endpoint 4096 3777)/2)
    have hp : upperPayment 3776 = (51802586156:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3776+point split endpoint 4096 3777)/2 = (671130527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671130527:ℝ)/168755200)*ClassicalSixthBranch.v ((671130527:ℝ)/168755200)/ClassicalSixthBranch.r = (79147048396625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3776
  · change upperPayment 3777 ≤ upperValue ((point split endpoint 4096 3777+point split endpoint 4096 3778)/2)
    have hp : upperPayment 3777 = (51646954513:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3777+point split endpoint 4096 3778)/2 = (671155677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671155677:ℝ)/168755200)*ClassicalSixthBranch.v ((671155677:ℝ)/168755200)/ClassicalSixthBranch.r = (79128675999705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3777
  · change upperPayment 3778 ≤ upperValue ((point split endpoint 4096 3778+point split endpoint 4096 3779)/2)
    have hp : upperPayment 3778 = (51491283193:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3778+point split endpoint 4096 3779)/2 = (671180827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671180827:ℝ)/168755200)*ClassicalSixthBranch.v ((671180827:ℝ)/168755200)/ClassicalSixthBranch.r = (79110305626857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3778
  · change upperPayment 3779 ≤ upperValue ((point split endpoint 4096 3779+point split endpoint 4096 3780)/2)
    have hp : upperPayment 3779 = (51335572186:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3779+point split endpoint 4096 3780)/2 = (671205977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671205977:ℝ)/168755200)*ClassicalSixthBranch.v ((671205977:ℝ)/168755200)/ClassicalSixthBranch.r = (79091937278081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3779
  · change upperPayment 3780 ≤ upperValue ((point split endpoint 4096 3780+point split endpoint 4096 3781)/2)
    have hp : upperPayment 3780 = (51179821481:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3780+point split endpoint 4096 3781)/2 = (671231127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671231127:ℝ)/168755200)*ClassicalSixthBranch.v ((671231127:ℝ)/168755200)/ClassicalSixthBranch.r = (79073570953377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3780
  · change upperPayment 3781 ≤ upperValue ((point split endpoint 4096 3781+point split endpoint 4096 3782)/2)
    have hp : upperPayment 3781 = (51024031067:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3781+point split endpoint 4096 3782)/2 = (671256277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671256277:ℝ)/168755200)*ClassicalSixthBranch.v ((671256277:ℝ)/168755200)/ClassicalSixthBranch.r = (79055206652745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3781
  · change upperPayment 3782 ≤ upperValue ((point split endpoint 4096 3782+point split endpoint 4096 3783)/2)
    have hp : upperPayment 3782 = (50868200933:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3782+point split endpoint 4096 3783)/2 = (671281427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671281427:ℝ)/168755200)*ClassicalSixthBranch.v ((671281427:ℝ)/168755200)/ClassicalSixthBranch.r = (79036844376185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3782
  · change upperPayment 3783 ≤ upperValue ((point split endpoint 4096 3783+point split endpoint 4096 3784)/2)
    have hp : upperPayment 3783 = (50712331069:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3783+point split endpoint 4096 3784)/2 = (671306577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671306577:ℝ)/168755200)*ClassicalSixthBranch.v ((671306577:ℝ)/168755200)/ClassicalSixthBranch.r = (79018484123697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3783
  · change upperPayment 3784 ≤ upperValue ((point split endpoint 4096 3784+point split endpoint 4096 3785)/2)
    have hp : upperPayment 3784 = (50556421464:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3784+point split endpoint 4096 3785)/2 = (671331727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671331727:ℝ)/168755200)*ClassicalSixthBranch.v ((671331727:ℝ)/168755200)/ClassicalSixthBranch.r = (79000125895281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3784
  · change upperPayment 3785 ≤ upperValue ((point split endpoint 4096 3785+point split endpoint 4096 3786)/2)
    have hp : upperPayment 3785 = (50400472108:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3785+point split endpoint 4096 3786)/2 = (671356877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671356877:ℝ)/168755200)*ClassicalSixthBranch.v ((671356877:ℝ)/168755200)/ClassicalSixthBranch.r = (78981769690937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3785
  · change upperPayment 3786 ≤ upperValue ((point split endpoint 4096 3786+point split endpoint 4096 3787)/2)
    have hp : upperPayment 3786 = (50244482989:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3786+point split endpoint 4096 3787)/2 = (671382027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671382027:ℝ)/168755200)*ClassicalSixthBranch.v ((671382027:ℝ)/168755200)/ClassicalSixthBranch.r = (78963415510665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3786
  · change upperPayment 3787 ≤ upperValue ((point split endpoint 4096 3787+point split endpoint 4096 3788)/2)
    have hp : upperPayment 3787 = (50088454097:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3787+point split endpoint 4096 3788)/2 = (671407177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671407177:ℝ)/168755200)*ClassicalSixthBranch.v ((671407177:ℝ)/168755200)/ClassicalSixthBranch.r = (78945063354465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3787
  · change upperPayment 3788 ≤ upperValue ((point split endpoint 4096 3788+point split endpoint 4096 3789)/2)
    have hp : upperPayment 3788 = (49932385422:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3788+point split endpoint 4096 3789)/2 = (671432327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671432327:ℝ)/168755200)*ClassicalSixthBranch.v ((671432327:ℝ)/168755200)/ClassicalSixthBranch.r = (78926713222337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3788
  · change upperPayment 3789 ≤ upperValue ((point split endpoint 4096 3789+point split endpoint 4096 3790)/2)
    have hp : upperPayment 3789 = (49776276952:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3789+point split endpoint 4096 3790)/2 = (671457477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671457477:ℝ)/168755200)*ClassicalSixthBranch.v ((671457477:ℝ)/168755200)/ClassicalSixthBranch.r = (78908365114281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3789
  · change upperPayment 3790 ≤ upperValue ((point split endpoint 4096 3790+point split endpoint 4096 3791)/2)
    have hp : upperPayment 3790 = (49620128676:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3790+point split endpoint 4096 3791)/2 = (671482627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671482627:ℝ)/168755200)*ClassicalSixthBranch.v ((671482627:ℝ)/168755200)/ClassicalSixthBranch.r = (78890019030297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3790
  · change upperPayment 3791 ≤ upperValue ((point split endpoint 4096 3791+point split endpoint 4096 3792)/2)
    have hp : upperPayment 3791 = (49463940585:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3791+point split endpoint 4096 3792)/2 = (671507777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((671507777:ℝ)/168755200)*ClassicalSixthBranch.v ((671507777:ℝ)/168755200)/ClassicalSixthBranch.r = (78871674970385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3791
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_236
