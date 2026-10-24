import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints244
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_244 (j : Fin 16) : upperPayment (16*244+j.val) ≤
    upperValue ((point split endpoint 4096 (16*244+j.val)+point split endpoint 4096 (16*244+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3904 ≤ upperValue ((point split endpoint 4096 3904+point split endpoint 4096 3905)/2)
    have hp : upperPayment 3904 = (31555548085:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3904+point split endpoint 4096 3905)/2 = (674349727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674349727:ℝ)/168755200)*ClassicalSixthBranch.v ((674349727:ℝ)/168755200)/ClassicalSixthBranch.r = (76811833248081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3904
  · change upperPayment 3905 ≤ upperValue ((point split endpoint 4096 3905+point split endpoint 4096 3906)/2)
    have hp : upperPayment 3905 = (31394749433:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3905+point split endpoint 4096 3906)/2 = (674374877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674374877:ℝ)/168755200)*ClassicalSixthBranch.v ((674374877:ℝ)/168755200)/ClassicalSixthBranch.r = (76793719932377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3905
  · change upperPayment 3906 ≤ upperValue ((point split endpoint 4096 3906+point split endpoint 4096 3907)/2)
    have hp : upperPayment 3906 = (31233909700:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3906+point split endpoint 4096 3907)/2 = (674400027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674400027:ℝ)/168755200)*ClassicalSixthBranch.v ((674400027:ℝ)/168755200)/ClassicalSixthBranch.r = (76775608640745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3906
  · change upperPayment 3907 ≤ upperValue ((point split endpoint 4096 3907+point split endpoint 4096 3908)/2)
    have hp : upperPayment 3907 = (31073028875:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3907+point split endpoint 4096 3908)/2 = (674425177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674425177:ℝ)/168755200)*ClassicalSixthBranch.v ((674425177:ℝ)/168755200)/ClassicalSixthBranch.r = (76757499373185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3907
  · change upperPayment 3908 ≤ upperValue ((point split endpoint 4096 3908+point split endpoint 4096 3909)/2)
    have hp : upperPayment 3908 = (30912106945:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3908+point split endpoint 4096 3909)/2 = (674450327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674450327:ℝ)/168755200)*ClassicalSixthBranch.v ((674450327:ℝ)/168755200)/ClassicalSixthBranch.r = (76739392129697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3908
  · change upperPayment 3909 ≤ upperValue ((point split endpoint 4096 3909+point split endpoint 4096 3910)/2)
    have hp : upperPayment 3909 = (30751143899:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3909+point split endpoint 4096 3910)/2 = (674475477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674475477:ℝ)/168755200)*ClassicalSixthBranch.v ((674475477:ℝ)/168755200)/ClassicalSixthBranch.r = (76721286910281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3909
  · change upperPayment 3910 ≤ upperValue ((point split endpoint 4096 3910+point split endpoint 4096 3911)/2)
    have hp : upperPayment 3910 = (30590139728:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3910+point split endpoint 4096 3911)/2 = (674500627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674500627:ℝ)/168755200)*ClassicalSixthBranch.v ((674500627:ℝ)/168755200)/ClassicalSixthBranch.r = (76703183714937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3910
  · change upperPayment 3911 ≤ upperValue ((point split endpoint 4096 3911+point split endpoint 4096 3912)/2)
    have hp : upperPayment 3911 = (30429094418:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3911+point split endpoint 4096 3912)/2 = (674525777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674525777:ℝ)/168755200)*ClassicalSixthBranch.v ((674525777:ℝ)/168755200)/ClassicalSixthBranch.r = (76685082543665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3911
  · change upperPayment 3912 ≤ upperValue ((point split endpoint 4096 3912+point split endpoint 4096 3913)/2)
    have hp : upperPayment 3912 = (30268007959:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3912+point split endpoint 4096 3913)/2 = (674550927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674550927:ℝ)/168755200)*ClassicalSixthBranch.v ((674550927:ℝ)/168755200)/ClassicalSixthBranch.r = (76666983396465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3912
  · change upperPayment 3913 ≤ upperValue ((point split endpoint 4096 3913+point split endpoint 4096 3914)/2)
    have hp : upperPayment 3913 = (30106880339:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3913+point split endpoint 4096 3914)/2 = (674576077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674576077:ℝ)/168755200)*ClassicalSixthBranch.v ((674576077:ℝ)/168755200)/ClassicalSixthBranch.r = (76648886273337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3913
  · change upperPayment 3914 ≤ upperValue ((point split endpoint 4096 3914+point split endpoint 4096 3915)/2)
    have hp : upperPayment 3914 = (29945711547:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3914+point split endpoint 4096 3915)/2 = (674601227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674601227:ℝ)/168755200)*ClassicalSixthBranch.v ((674601227:ℝ)/168755200)/ClassicalSixthBranch.r = (76630791174281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3914
  · change upperPayment 3915 ≤ upperValue ((point split endpoint 4096 3915+point split endpoint 4096 3916)/2)
    have hp : upperPayment 3915 = (29784501573:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3915+point split endpoint 4096 3916)/2 = (674626377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674626377:ℝ)/168755200)*ClassicalSixthBranch.v ((674626377:ℝ)/168755200)/ClassicalSixthBranch.r = (76612698099297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3915
  · change upperPayment 3916 ≤ upperValue ((point split endpoint 4096 3916+point split endpoint 4096 3917)/2)
    have hp : upperPayment 3916 = (29623250403:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3916+point split endpoint 4096 3917)/2 = (674651527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674651527:ℝ)/168755200)*ClassicalSixthBranch.v ((674651527:ℝ)/168755200)/ClassicalSixthBranch.r = (76594607048385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3916
  · change upperPayment 3917 ≤ upperValue ((point split endpoint 4096 3917+point split endpoint 4096 3918)/2)
    have hp : upperPayment 3917 = (29461958028:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3917+point split endpoint 4096 3918)/2 = (6550259:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6550259:ℝ)/1638400)*ClassicalSixthBranch.v ((6550259:ℝ)/1638400)/ClassicalSixthBranch.r = (743461340015:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3917
  · change upperPayment 3918 ≤ upperValue ((point split endpoint 4096 3918+point split endpoint 4096 3919)/2)
    have hp : upperPayment 3918 = (29300624436:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3918+point split endpoint 4096 3919)/2 = (674701827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674701827:ℝ)/168755200)*ClassicalSixthBranch.v ((674701827:ℝ)/168755200)/ClassicalSixthBranch.r = (76558431018777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3918
  · change upperPayment 3919 ≤ upperValue ((point split endpoint 4096 3919+point split endpoint 4096 3920)/2)
    have hp : upperPayment 3919 = (29139249615:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3919+point split endpoint 4096 3920)/2 = (674726977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674726977:ℝ)/168755200)*ClassicalSixthBranch.v ((674726977:ℝ)/168755200)/ClassicalSixthBranch.r = (76540346040081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3919
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_244
