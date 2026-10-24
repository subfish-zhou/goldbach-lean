import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints054
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_054 (j : Fin 16) : upperPayment (16*54+j.val) ≤
    upperValue ((point split endpoint 4096 (16*54+j.val)+point split endpoint 4096 (16*54+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 864 ≤ upperValue ((point split endpoint 4096 864+point split endpoint 4096 865)/2)
    have hp : upperPayment 864 = (370120303465:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 864+point split endpoint 4096 865)/2 = (597893727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597893727:ℝ)/168755200)*ClassicalSixthBranch.v ((597893727:ℝ)/168755200)/ClassicalSixthBranch.r = (141232221475281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_864
  · change upperPayment 865 ≤ upperValue ((point split endpoint 4096 865+point split endpoint 4096 866)/2)
    have hp : upperPayment 865 = (370048673123:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 865+point split endpoint 4096 866)/2 = (597918877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597918877:ℝ)/168755200)*ClassicalSixthBranch.v ((597918877:ℝ)/168755200)/ClassicalSixthBranch.r = (141207954980697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_865
  · change upperPayment 866 ≤ upperValue ((point split endpoint 4096 866+point split endpoint 4096 867)/2)
    have hp : upperPayment 866 = (369977021251:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 866+point split endpoint 4096 867)/2 = (597944027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597944027:ℝ)/168755200)*ClassicalSixthBranch.v ((597944027:ℝ)/168755200)/ClassicalSixthBranch.r = (141183690510185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_866
  · change upperPayment 867 ≤ upperValue ((point split endpoint 4096 867+point split endpoint 4096 868)/2)
    have hp : upperPayment 867 = (369905347846:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 867+point split endpoint 4096 868)/2 = (597969177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597969177:ℝ)/168755200)*ClassicalSixthBranch.v ((597969177:ℝ)/168755200)/ClassicalSixthBranch.r = (141159428063745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_867
  · change upperPayment 868 ≤ upperValue ((point split endpoint 4096 868+point split endpoint 4096 869)/2)
    have hp : upperPayment 868 = (369833652905:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 868+point split endpoint 4096 869)/2 = (597994327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((597994327:ℝ)/168755200)*ClassicalSixthBranch.v ((597994327:ℝ)/168755200)/ClassicalSixthBranch.r = (141135167641377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_868
  · change upperPayment 869 ≤ upperValue ((point split endpoint 4096 869+point split endpoint 4096 870)/2)
    have hp : upperPayment 869 = (369761936424:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 869+point split endpoint 4096 870)/2 = (598019477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598019477:ℝ)/168755200)*ClassicalSixthBranch.v ((598019477:ℝ)/168755200)/ClassicalSixthBranch.r = (141110909243081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_869
  · change upperPayment 870 ≤ upperValue ((point split endpoint 4096 870+point split endpoint 4096 871)/2)
    have hp : upperPayment 870 = (369690198402:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 870+point split endpoint 4096 871)/2 = (598044627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598044627:ℝ)/168755200)*ClassicalSixthBranch.v ((598044627:ℝ)/168755200)/ClassicalSixthBranch.r = (141086652868857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_870
  · change upperPayment 871 ≤ upperValue ((point split endpoint 4096 871+point split endpoint 4096 872)/2)
    have hp : upperPayment 871 = (369618438834:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 871+point split endpoint 4096 872)/2 = (598069777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598069777:ℝ)/168755200)*ClassicalSixthBranch.v ((598069777:ℝ)/168755200)/ClassicalSixthBranch.r = (141062398518705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_871
  · change upperPayment 872 ≤ upperValue ((point split endpoint 4096 872+point split endpoint 4096 873)/2)
    have hp : upperPayment 872 = (369546657717:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 872+point split endpoint 4096 873)/2 = (598094927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598094927:ℝ)/168755200)*ClassicalSixthBranch.v ((598094927:ℝ)/168755200)/ClassicalSixthBranch.r = (141038146192625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_872
  · change upperPayment 873 ≤ upperValue ((point split endpoint 4096 873+point split endpoint 4096 874)/2)
    have hp : upperPayment 873 = (369474855047:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 873+point split endpoint 4096 874)/2 = (598120077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598120077:ℝ)/168755200)*ClassicalSixthBranch.v ((598120077:ℝ)/168755200)/ClassicalSixthBranch.r = (141013895890617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_873
  · change upperPayment 874 ≤ upperValue ((point split endpoint 4096 874+point split endpoint 4096 875)/2)
    have hp : upperPayment 874 = (369403030823:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 874+point split endpoint 4096 875)/2 = (598145227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598145227:ℝ)/168755200)*ClassicalSixthBranch.v ((598145227:ℝ)/168755200)/ClassicalSixthBranch.r = (140989647612681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_874
  · change upperPayment 875 ≤ upperValue ((point split endpoint 4096 875+point split endpoint 4096 876)/2)
    have hp : upperPayment 875 = (369331185040:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 875+point split endpoint 4096 876)/2 = (598170377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598170377:ℝ)/168755200)*ClassicalSixthBranch.v ((598170377:ℝ)/168755200)/ClassicalSixthBranch.r = (140965401358817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_875
  · change upperPayment 876 ≤ upperValue ((point split endpoint 4096 876+point split endpoint 4096 877)/2)
    have hp : upperPayment 876 = (369259317695:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 876+point split endpoint 4096 877)/2 = (598195527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598195527:ℝ)/168755200)*ClassicalSixthBranch.v ((598195527:ℝ)/168755200)/ClassicalSixthBranch.r = (140941157129025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_876
  · change upperPayment 877 ≤ upperValue ((point split endpoint 4096 877+point split endpoint 4096 878)/2)
    have hp : upperPayment 877 = (369187428785:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 877+point split endpoint 4096 878)/2 = (598220677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598220677:ℝ)/168755200)*ClassicalSixthBranch.v ((598220677:ℝ)/168755200)/ClassicalSixthBranch.r = (140916914923305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_877
  · change upperPayment 878 ≤ upperValue ((point split endpoint 4096 878+point split endpoint 4096 879)/2)
    have hp : upperPayment 878 = (369115518307:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 878+point split endpoint 4096 879)/2 = (598245827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598245827:ℝ)/168755200)*ClassicalSixthBranch.v ((598245827:ℝ)/168755200)/ClassicalSixthBranch.r = (140892674741657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_878
  · change upperPayment 879 ≤ upperValue ((point split endpoint 4096 879+point split endpoint 4096 880)/2)
    have hp : upperPayment 879 = (369043586258:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 879+point split endpoint 4096 880)/2 = (598270977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598270977:ℝ)/168755200)*ClassicalSixthBranch.v ((598270977:ℝ)/168755200)/ClassicalSixthBranch.r = (140868436584081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_879
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_054
