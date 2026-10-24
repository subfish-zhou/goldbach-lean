import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints207
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_207 (j : Fin 16) : upperPayment (16*207+j.val) ≤
    upperValue ((point split endpoint 4096 (16*207+j.val)+point split endpoint 4096 (16*207+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3312 ≤ upperValue ((point split endpoint 4096 3312+point split endpoint 4096 3313)/2)
    have hp : upperPayment 3312 = (119905830253:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3312+point split endpoint 4096 3313)/2 = (659460927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659460927:ℝ)/168755200)*ClassicalSixthBranch.v ((659460927:ℝ)/168755200)/ClassicalSixthBranch.r = (87890197454865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3312
  · change upperPayment 3313 ≤ upperValue ((point split endpoint 4096 3313+point split endpoint 4096 3314)/2)
    have hp : upperPayment 3313 = (119767528282:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3313+point split endpoint 4096 3314)/2 = (659486077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659486077:ℝ)/168755200)*ClassicalSixthBranch.v ((659486077:ℝ)/168755200)/ClassicalSixthBranch.r = (87870885888537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3313
  · change upperPayment 3314 ≤ upperValue ((point split endpoint 4096 3314+point split endpoint 4096 3315)/2)
    have hp : upperPayment 3314 = (119629191136:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3314+point split endpoint 4096 3315)/2 = (659511227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659511227:ℝ)/168755200)*ClassicalSixthBranch.v ((659511227:ℝ)/168755200)/ClassicalSixthBranch.r = (87851576346281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3314
  · change upperPayment 3315 ≤ upperValue ((point split endpoint 4096 3315+point split endpoint 4096 3316)/2)
    have hp : upperPayment 3315 = (119490818806:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3315+point split endpoint 4096 3316)/2 = (659536377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659536377:ℝ)/168755200)*ClassicalSixthBranch.v ((659536377:ℝ)/168755200)/ClassicalSixthBranch.r = (87832268828097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3315
  · change upperPayment 3316 ≤ upperValue ((point split endpoint 4096 3316+point split endpoint 4096 3317)/2)
    have hp : upperPayment 3316 = (119352411283:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3316+point split endpoint 4096 3317)/2 = (659561527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659561527:ℝ)/168755200)*ClassicalSixthBranch.v ((659561527:ℝ)/168755200)/ClassicalSixthBranch.r = (87812963333985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3316
  · change upperPayment 3317 ≤ upperValue ((point split endpoint 4096 3317+point split endpoint 4096 3318)/2)
    have hp : upperPayment 3317 = (119213968559:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3317+point split endpoint 4096 3318)/2 = (659586677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659586677:ℝ)/168755200)*ClassicalSixthBranch.v ((659586677:ℝ)/168755200)/ClassicalSixthBranch.r = (66159502535:ℝ)/55297703936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3317
  · change upperPayment 3318 ≤ upperValue ((point split endpoint 4096 3318+point split endpoint 4096 3319)/2)
    have hp : upperPayment 3318 = (119075490624:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3318+point split endpoint 4096 3319)/2 = (659611827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659611827:ℝ)/168755200)*ClassicalSixthBranch.v ((659611827:ℝ)/168755200)/ClassicalSixthBranch.r = (87774358417977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3318
  · change upperPayment 3319 ≤ upperValue ((point split endpoint 4096 3319+point split endpoint 4096 3320)/2)
    have hp : upperPayment 3319 = (118936977470:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3319+point split endpoint 4096 3320)/2 = (659636977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659636977:ℝ)/168755200)*ClassicalSixthBranch.v ((659636977:ℝ)/168755200)/ClassicalSixthBranch.r = (87755058996081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3319
  · change upperPayment 3320 ≤ upperValue ((point split endpoint 4096 3320+point split endpoint 4096 3321)/2)
    have hp : upperPayment 3320 = (118798429088:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3320+point split endpoint 4096 3321)/2 = (659662127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659662127:ℝ)/168755200)*ClassicalSixthBranch.v ((659662127:ℝ)/168755200)/ClassicalSixthBranch.r = (87735761598257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3320
  · change upperPayment 3321 ≤ upperValue ((point split endpoint 4096 3321+point split endpoint 4096 3322)/2)
    have hp : upperPayment 3321 = (118659845470:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3321+point split endpoint 4096 3322)/2 = (659687277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659687277:ℝ)/168755200)*ClassicalSixthBranch.v ((659687277:ℝ)/168755200)/ClassicalSixthBranch.r = (87716466224505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3321
  · change upperPayment 3322 ≤ upperValue ((point split endpoint 4096 3322+point split endpoint 4096 3323)/2)
    have hp : upperPayment 3322 = (118521226606:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3322+point split endpoint 4096 3323)/2 = (659712427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659712427:ℝ)/168755200)*ClassicalSixthBranch.v ((659712427:ℝ)/168755200)/ClassicalSixthBranch.r = (87697172874825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3322
  · change upperPayment 3323 ≤ upperValue ((point split endpoint 4096 3323+point split endpoint 4096 3324)/2)
    have hp : upperPayment 3323 = (118382572487:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3323+point split endpoint 4096 3324)/2 = (659737577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659737577:ℝ)/168755200)*ClassicalSixthBranch.v ((659737577:ℝ)/168755200)/ClassicalSixthBranch.r = (851241568439:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3323
  · change upperPayment 3324 ≤ upperValue ((point split endpoint 4096 3324+point split endpoint 4096 3325)/2)
    have hp : upperPayment 3324 = (118243883105:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3324+point split endpoint 4096 3325)/2 = (659762727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659762727:ℝ)/168755200)*ClassicalSixthBranch.v ((659762727:ℝ)/168755200)/ClassicalSixthBranch.r = (87658592247681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3324
  · change upperPayment 3325 ≤ upperValue ((point split endpoint 4096 3325+point split endpoint 4096 3326)/2)
    have hp : upperPayment 3325 = (118105158451:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3325+point split endpoint 4096 3326)/2 = (659787877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659787877:ℝ)/168755200)*ClassicalSixthBranch.v ((659787877:ℝ)/168755200)/ClassicalSixthBranch.r = (87639304970217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3325
  · change upperPayment 3326 ≤ upperValue ((point split endpoint 4096 3326+point split endpoint 4096 3327)/2)
    have hp : upperPayment 3326 = (117966398516:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3326+point split endpoint 4096 3327)/2 = (659813027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659813027:ℝ)/168755200)*ClassicalSixthBranch.v ((659813027:ℝ)/168755200)/ClassicalSixthBranch.r = (87620019716825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3326
  · change upperPayment 3327 ≤ upperValue ((point split endpoint 4096 3327+point split endpoint 4096 3328)/2)
    have hp : upperPayment 3327 = (117827603291:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3327+point split endpoint 4096 3328)/2 = (659838177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659838177:ℝ)/168755200)*ClassicalSixthBranch.v ((659838177:ℝ)/168755200)/ClassicalSixthBranch.r = (87600736487505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3327
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_207
