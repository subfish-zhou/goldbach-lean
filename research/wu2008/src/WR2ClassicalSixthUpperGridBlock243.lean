import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints243
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_243 (j : Fin 16) : upperPayment (16*243+j.val) ≤
    upperValue ((point split endpoint 4096 (16*243+j.val)+point split endpoint 4096 (16*243+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3888 ≤ upperValue ((point split endpoint 4096 3888+point split endpoint 4096 3889)/2)
    have hp : upperPayment 3888 = (34122748612:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3888+point split endpoint 4096 3889)/2 = (673947327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673947327:ℝ)/168755200)*ClassicalSixthBranch.v ((673947327:ℝ)/168755200)/ClassicalSixthBranch.r = (77101921573137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3888
  · change upperPayment 3889 ≤ upperValue ((point split endpoint 4096 3889+point split endpoint 4096 3890)/2)
    have hp : upperPayment 3889 = (33962605734:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3889+point split endpoint 4096 3890)/2 = (673972477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673972477:ℝ)/168755200)*ClassicalSixthBranch.v ((673972477:ℝ)/168755200)/ClassicalSixthBranch.r = (77083775872281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3889
  · change upperPayment 3890 ≤ upperValue ((point split endpoint 4096 3890+point split endpoint 4096 3891)/2)
    have hp : upperPayment 3890 = (33802421955:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3890+point split endpoint 4096 3891)/2 = (673997627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673997627:ℝ)/168755200)*ClassicalSixthBranch.v ((673997627:ℝ)/168755200)/ClassicalSixthBranch.r = (77065632195497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3890
  · change upperPayment 3891 ≤ upperValue ((point split endpoint 4096 3891+point split endpoint 4096 3892)/2)
    have hp : upperPayment 3891 = (33642197263:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3891+point split endpoint 4096 3892)/2 = (674022777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674022777:ℝ)/168755200)*ClassicalSixthBranch.v ((674022777:ℝ)/168755200)/ClassicalSixthBranch.r = (77047490542785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3891
  · change upperPayment 3892 ≤ upperValue ((point split endpoint 4096 3892+point split endpoint 4096 3893)/2)
    have hp : upperPayment 3892 = (33481931646:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3892+point split endpoint 4096 3893)/2 = (674047927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674047927:ℝ)/168755200)*ClassicalSixthBranch.v ((674047927:ℝ)/168755200)/ClassicalSixthBranch.r = (77029350914145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3892
  · change upperPayment 3893 ≤ upperValue ((point split endpoint 4096 3893+point split endpoint 4096 3894)/2)
    have hp : upperPayment 3893 = (33321625095:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3893+point split endpoint 4096 3894)/2 = (674073077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674073077:ℝ)/168755200)*ClassicalSixthBranch.v ((674073077:ℝ)/168755200)/ClassicalSixthBranch.r = (77011213309577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3893
  · change upperPayment 3894 ≤ upperValue ((point split endpoint 4096 3894+point split endpoint 4096 3895)/2)
    have hp : upperPayment 3894 = (33161277597:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3894+point split endpoint 4096 3895)/2 = (674098227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674098227:ℝ)/168755200)*ClassicalSixthBranch.v ((674098227:ℝ)/168755200)/ClassicalSixthBranch.r = (76993077729081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3894
  · change upperPayment 3895 ≤ upperValue ((point split endpoint 4096 3895+point split endpoint 4096 3896)/2)
    have hp : upperPayment 3895 = (33000889141:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3895+point split endpoint 4096 3896)/2 = (674123377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674123377:ℝ)/168755200)*ClassicalSixthBranch.v ((674123377:ℝ)/168755200)/ClassicalSixthBranch.r = (76974944172657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3895
  · change upperPayment 3896 ≤ upperValue ((point split endpoint 4096 3896+point split endpoint 4096 3897)/2)
    have hp : upperPayment 3896 = (32840459716:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3896+point split endpoint 4096 3897)/2 = (674148527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674148527:ℝ)/168755200)*ClassicalSixthBranch.v ((674148527:ℝ)/168755200)/ClassicalSixthBranch.r = (76956812640305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3896
  · change upperPayment 3897 ≤ upperValue ((point split endpoint 4096 3897+point split endpoint 4096 3898)/2)
    have hp : upperPayment 3897 = (32679989311:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3897+point split endpoint 4096 3898)/2 = (674173677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674173677:ℝ)/168755200)*ClassicalSixthBranch.v ((674173677:ℝ)/168755200)/ClassicalSixthBranch.r = (76938683132025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3897
  · change upperPayment 3898 ≤ upperValue ((point split endpoint 4096 3898+point split endpoint 4096 3899)/2)
    have hp : upperPayment 3898 = (32519477914:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3898+point split endpoint 4096 3899)/2 = (674198827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674198827:ℝ)/168755200)*ClassicalSixthBranch.v ((674198827:ℝ)/168755200)/ClassicalSixthBranch.r = (76920555647817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3898
  · change upperPayment 3899 ≤ upperValue ((point split endpoint 4096 3899+point split endpoint 4096 3900)/2)
    have hp : upperPayment 3899 = (32358925515:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3899+point split endpoint 4096 3900)/2 = (674223977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674223977:ℝ)/168755200)*ClassicalSixthBranch.v ((674223977:ℝ)/168755200)/ClassicalSixthBranch.r = (76902430187681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3899
  · change upperPayment 3900 ≤ upperValue ((point split endpoint 4096 3900+point split endpoint 4096 3901)/2)
    have hp : upperPayment 3900 = (32198332102:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3900+point split endpoint 4096 3901)/2 = (674249127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674249127:ℝ)/168755200)*ClassicalSixthBranch.v ((674249127:ℝ)/168755200)/ClassicalSixthBranch.r = (76884306751617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3900
  · change upperPayment 3901 ≤ upperValue ((point split endpoint 4096 3901+point split endpoint 4096 3902)/2)
    have hp : upperPayment 3901 = (32037697664:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3901+point split endpoint 4096 3902)/2 = (674274277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674274277:ℝ)/168755200)*ClassicalSixthBranch.v ((674274277:ℝ)/168755200)/ClassicalSixthBranch.r = (76866185339625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3901
  · change upperPayment 3902 ≤ upperValue ((point split endpoint 4096 3902+point split endpoint 4096 3903)/2)
    have hp : upperPayment 3902 = (31877022189:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3902+point split endpoint 4096 3903)/2 = (674299427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674299427:ℝ)/168755200)*ClassicalSixthBranch.v ((674299427:ℝ)/168755200)/ClassicalSixthBranch.r = (76848065951705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3902
  · change upperPayment 3903 ≤ upperValue ((point split endpoint 4096 3903+point split endpoint 4096 3904)/2)
    have hp : upperPayment 3903 = (31716305666:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3903+point split endpoint 4096 3904)/2 = (674324577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674324577:ℝ)/168755200)*ClassicalSixthBranch.v ((674324577:ℝ)/168755200)/ClassicalSixthBranch.r = (76829948587857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3903
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_243
