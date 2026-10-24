import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints246
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_246 (j : Fin 16) : upperPayment (16*246+j.val) ≤
    upperValue ((point split endpoint 4096 (16*246+j.val)+point split endpoint 4096 (16*246+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3936 ≤ upperValue ((point split endpoint 4096 3936+point split endpoint 4096 3937)/2)
    have hp : upperPayment 3936 = (26389558690:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3936+point split endpoint 4096 3937)/2 = (675154527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675154527:ℝ)/168755200)*ClassicalSixthBranch.v ((675154527:ℝ)/168755200)/ClassicalSixthBranch.r = (76233211085265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3936
  · change upperPayment 3937 ≤ upperValue ((point split endpoint 4096 3937+point split endpoint 4096 3938)/2)
    have hp : upperPayment 3937 = (26227439812:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3937+point split endpoint 4096 3938)/2 = (675179677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675179677:ℝ)/168755200)*ClassicalSixthBranch.v ((675179677:ℝ)/168755200)/ClassicalSixthBranch.r = (76215162539865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3937
  · change upperPayment 3938 ≤ upperValue ((point split endpoint 4096 3938+point split endpoint 4096 3939)/2)
    have hp : upperPayment 3938 = (26065279489:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3938+point split endpoint 4096 3939)/2 = (675204827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675204827:ℝ)/168755200)*ClassicalSixthBranch.v ((675204827:ℝ)/168755200)/ClassicalSixthBranch.r = (76197116018537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3938
  · change upperPayment 3939 ≤ upperValue ((point split endpoint 4096 3939+point split endpoint 4096 3940)/2)
    have hp : upperPayment 3939 = (25903077709:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3939+point split endpoint 4096 3940)/2 = (675229977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675229977:ℝ)/168755200)*ClassicalSixthBranch.v ((675229977:ℝ)/168755200)/ClassicalSixthBranch.r = (76179071521281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3939
  · change upperPayment 3940 ≤ upperValue ((point split endpoint 4096 3940+point split endpoint 4096 3941)/2)
    have hp : upperPayment 3940 = (25740834462:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3940+point split endpoint 4096 3941)/2 = (675255127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675255127:ℝ)/168755200)*ClassicalSixthBranch.v ((675255127:ℝ)/168755200)/ClassicalSixthBranch.r = (76161029048097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3940
  · change upperPayment 3941 ≤ upperValue ((point split endpoint 4096 3941+point split endpoint 4096 3942)/2)
    have hp : upperPayment 3941 = (25578549735:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3941+point split endpoint 4096 3942)/2 = (675280277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675280277:ℝ)/168755200)*ClassicalSixthBranch.v ((675280277:ℝ)/168755200)/ClassicalSixthBranch.r = (739252316495:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3941
  · change upperPayment 3942 ≤ upperValue ((point split endpoint 4096 3942+point split endpoint 4096 3943)/2)
    have hp : upperPayment 3942 = (25416223518:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3942+point split endpoint 4096 3943)/2 = (675305427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675305427:ℝ)/168755200)*ClassicalSixthBranch.v ((675305427:ℝ)/168755200)/ClassicalSixthBranch.r = (76124950173945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3942
  · change upperPayment 3943 ≤ upperValue ((point split endpoint 4096 3943+point split endpoint 4096 3944)/2)
    have hp : upperPayment 3943 = (25253855799:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3943+point split endpoint 4096 3944)/2 = (675330577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675330577:ℝ)/168755200)*ClassicalSixthBranch.v ((675330577:ℝ)/168755200)/ClassicalSixthBranch.r = (76106913772977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3943
  · change upperPayment 3944 ≤ upperValue ((point split endpoint 4096 3944+point split endpoint 4096 3945)/2)
    have hp : upperPayment 3944 = (25091446566:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3944+point split endpoint 4096 3945)/2 = (675355727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675355727:ℝ)/168755200)*ClassicalSixthBranch.v ((675355727:ℝ)/168755200)/ClassicalSixthBranch.r = (76088879396081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3944
  · change upperPayment 3945 ≤ upperValue ((point split endpoint 4096 3945+point split endpoint 4096 3946)/2)
    have hp : upperPayment 3945 = (24928995809:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3945+point split endpoint 4096 3946)/2 = (675380877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675380877:ℝ)/168755200)*ClassicalSixthBranch.v ((675380877:ℝ)/168755200)/ClassicalSixthBranch.r = (76070847043257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3945
  · change upperPayment 3946 ≤ upperValue ((point split endpoint 4096 3946+point split endpoint 4096 3947)/2)
    have hp : upperPayment 3946 = (24766503514:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3946+point split endpoint 4096 3947)/2 = (675406027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675406027:ℝ)/168755200)*ClassicalSixthBranch.v ((675406027:ℝ)/168755200)/ClassicalSixthBranch.r = (76052816714505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3946
  · change upperPayment 3947 ≤ upperValue ((point split endpoint 4096 3947+point split endpoint 4096 3948)/2)
    have hp : upperPayment 3947 = (24603969672:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3947+point split endpoint 4096 3948)/2 = (675431177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675431177:ℝ)/168755200)*ClassicalSixthBranch.v ((675431177:ℝ)/168755200)/ClassicalSixthBranch.r = (76034788409825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3947
  · change upperPayment 3948 ≤ upperValue ((point split endpoint 4096 3948+point split endpoint 4096 3949)/2)
    have hp : upperPayment 3948 = (24441394271:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3948+point split endpoint 4096 3949)/2 = (675456327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675456327:ℝ)/168755200)*ClassicalSixthBranch.v ((675456327:ℝ)/168755200)/ClassicalSixthBranch.r = (76016762129217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3948
  · change upperPayment 3949 ≤ upperValue ((point split endpoint 4096 3949+point split endpoint 4096 3950)/2)
    have hp : upperPayment 3949 = (24278777298:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3949+point split endpoint 4096 3950)/2 = (675481477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675481477:ℝ)/168755200)*ClassicalSixthBranch.v ((675481477:ℝ)/168755200)/ClassicalSixthBranch.r = (75998737872681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3949
  · change upperPayment 3950 ≤ upperValue ((point split endpoint 4096 3950+point split endpoint 4096 3951)/2)
    have hp : upperPayment 3950 = (24116118743:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3950+point split endpoint 4096 3951)/2 = (675506627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675506627:ℝ)/168755200)*ClassicalSixthBranch.v ((675506627:ℝ)/168755200)/ClassicalSixthBranch.r = (75980715640217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3950
  · change upperPayment 3951 ≤ upperValue ((point split endpoint 4096 3951+point split endpoint 4096 3952)/2)
    have hp : upperPayment 3951 = (23953418594:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3951+point split endpoint 4096 3952)/2 = (675531777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675531777:ℝ)/168755200)*ClassicalSixthBranch.v ((675531777:ℝ)/168755200)/ClassicalSixthBranch.r = (75962695431825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3951
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_246
