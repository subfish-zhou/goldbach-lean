import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints019
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_019 (j : Fin 16) : upperPayment (16*19+j.val) ≤
    upperValue ((point split endpoint 4096 (16*19+j.val)+point split endpoint 4096 (16*19+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 304 ≤ upperValue ((point split endpoint 4096 304+point split endpoint 4096 305)/2)
    have hp : upperPayment 304 = (406940269212:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 304+point split endpoint 4096 305)/2 = (583809727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583809727:ℝ)/168755200)*ClassicalSixthBranch.v ((583809727:ℝ)/168755200)/ClassicalSixthBranch.r = (155139399672081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_304
  · change upperPayment 305 ≤ upperValue ((point split endpoint 4096 305+point split endpoint 4096 306)/2)
    have hp : upperPayment 305 = (406880231083:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 305+point split endpoint 4096 306)/2 = (583834877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583834877:ℝ)/168755200)*ClassicalSixthBranch.v ((583834877:ℝ)/168755200)/ClassicalSixthBranch.r = (155113999697177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_305
  · change upperPayment 306 ≤ upperValue ((point split endpoint 4096 306+point split endpoint 4096 307)/2)
    have hp : upperPayment 306 = (406820173010:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 306+point split endpoint 4096 307)/2 = (583860027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583860027:ℝ)/168755200)*ClassicalSixthBranch.v ((583860027:ℝ)/168755200)/ClassicalSixthBranch.r = (155088601746345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_306
  · change upperPayment 307 ≤ upperValue ((point split endpoint 4096 307+point split endpoint 4096 308)/2)
    have hp : upperPayment 307 = (406760094992:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 307+point split endpoint 4096 308)/2 = (583885177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583885177:ℝ)/168755200)*ClassicalSixthBranch.v ((583885177:ℝ)/168755200)/ClassicalSixthBranch.r = (155063205819585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_307
  · change upperPayment 308 ≤ upperValue ((point split endpoint 4096 308+point split endpoint 4096 309)/2)
    have hp : upperPayment 308 = (406699997025:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 308+point split endpoint 4096 309)/2 = (583910327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583910327:ℝ)/168755200)*ClassicalSixthBranch.v ((583910327:ℝ)/168755200)/ClassicalSixthBranch.r = (155037811916897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_308
  · change upperPayment 309 ≤ upperValue ((point split endpoint 4096 309+point split endpoint 4096 310)/2)
    have hp : upperPayment 309 = (406639879107:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 309+point split endpoint 4096 310)/2 = (583935477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583935477:ℝ)/168755200)*ClassicalSixthBranch.v ((583935477:ℝ)/168755200)/ClassicalSixthBranch.r = (155012420038281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_309
  · change upperPayment 310 ≤ upperValue ((point split endpoint 4096 310+point split endpoint 4096 311)/2)
    have hp : upperPayment 310 = (406579741235:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 310+point split endpoint 4096 311)/2 = (583960627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583960627:ℝ)/168755200)*ClassicalSixthBranch.v ((583960627:ℝ)/168755200)/ClassicalSixthBranch.r = (154987030183737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_310
  · change upperPayment 311 ≤ upperValue ((point split endpoint 4096 311+point split endpoint 4096 312)/2)
    have hp : upperPayment 311 = (406519583408:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 311+point split endpoint 4096 312)/2 = (583985777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((583985777:ℝ)/168755200)*ClassicalSixthBranch.v ((583985777:ℝ)/168755200)/ClassicalSixthBranch.r = (154961642353265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_311
  · change upperPayment 312 ≤ upperValue ((point split endpoint 4096 312+point split endpoint 4096 313)/2)
    have hp : upperPayment 312 = (406459405622:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 312+point split endpoint 4096 313)/2 = (5670009:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5670009:ℝ)/1638400)*ClassicalSixthBranch.v ((5670009:ℝ)/1638400)/ClassicalSixthBranch.r = (1504235500455:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_312
  · change upperPayment 313 ≤ upperValue ((point split endpoint 4096 313+point split endpoint 4096 314)/2)
    have hp : upperPayment 313 = (406399207875:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 313+point split endpoint 4096 314)/2 = (584036077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584036077:ℝ)/168755200)*ClassicalSixthBranch.v ((584036077:ℝ)/168755200)/ClassicalSixthBranch.r = (154910872764537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_313
  · change upperPayment 314 ≤ upperValue ((point split endpoint 4096 314+point split endpoint 4096 315)/2)
    have hp : upperPayment 314 = (406338990165:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 314+point split endpoint 4096 315)/2 = (584061227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584061227:ℝ)/168755200)*ClassicalSixthBranch.v ((584061227:ℝ)/168755200)/ClassicalSixthBranch.r = (154885491006281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_314
  · change upperPayment 315 ≤ upperValue ((point split endpoint 4096 315+point split endpoint 4096 316)/2)
    have hp : upperPayment 315 = (406278752489:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 315+point split endpoint 4096 316)/2 = (584086377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584086377:ℝ)/168755200)*ClassicalSixthBranch.v ((584086377:ℝ)/168755200)/ClassicalSixthBranch.r = (154860111272097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_315
  · change upperPayment 316 ≤ upperValue ((point split endpoint 4096 316+point split endpoint 4096 317)/2)
    have hp : upperPayment 316 = (406218494845:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 316+point split endpoint 4096 317)/2 = (584111527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584111527:ℝ)/168755200)*ClassicalSixthBranch.v ((584111527:ℝ)/168755200)/ClassicalSixthBranch.r = (154834733561985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_316
  · change upperPayment 317 ≤ upperValue ((point split endpoint 4096 317+point split endpoint 4096 318)/2)
    have hp : upperPayment 317 = (406158217230:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 317+point split endpoint 4096 318)/2 = (584136677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584136677:ℝ)/168755200)*ClassicalSixthBranch.v ((584136677:ℝ)/168755200)/ClassicalSixthBranch.r = (154809357875945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_317
  · change upperPayment 318 ≤ upperValue ((point split endpoint 4096 318+point split endpoint 4096 319)/2)
    have hp : upperPayment 318 = (406097919641:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 318+point split endpoint 4096 319)/2 = (584161827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584161827:ℝ)/168755200)*ClassicalSixthBranch.v ((584161827:ℝ)/168755200)/ClassicalSixthBranch.r = (154783984213977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_318
  · change upperPayment 319 ≤ upperValue ((point split endpoint 4096 319+point split endpoint 4096 320)/2)
    have hp : upperPayment 319 = (406037602077:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 319+point split endpoint 4096 320)/2 = (584186977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((584186977:ℝ)/168755200)*ClassicalSixthBranch.v ((584186977:ℝ)/168755200)/ClassicalSixthBranch.r = (154758612576081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_319
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_019
