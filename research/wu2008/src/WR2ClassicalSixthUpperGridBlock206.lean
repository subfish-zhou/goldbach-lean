import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints206
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_206 (j : Fin 16) : upperPayment (16*206+j.val) ≤
    upperValue ((point split endpoint 4096 (16*206+j.val)+point split endpoint 4096 (16*206+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3296 ≤ upperValue ((point split endpoint 4096 3296+point split endpoint 4096 3297)/2)
    have hp : upperPayment 3296 = (122113885133:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3296+point split endpoint 4096 3297)/2 = (659058527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659058527:ℝ)/168755200)*ClassicalSixthBranch.v ((659058527:ℝ)/168755200)/ClassicalSixthBranch.r = (88199457789905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3296
  · change upperPayment 3297 ≤ upperValue ((point split endpoint 4096 3297+point split endpoint 4096 3298)/2)
    have hp : upperPayment 3297 = (121976144770:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3297+point split endpoint 4096 3298)/2 = (659083677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659083677:ℝ)/168755200)*ClassicalSixthBranch.v ((659083677:ℝ)/168755200)/ClassicalSixthBranch.r = (88180113838425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3297
  · change upperPayment 3298 ≤ upperValue ((point split endpoint 4096 3298+point split endpoint 4096 3299)/2)
    have hp : upperPayment 3298 = (121838369373:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3298+point split endpoint 4096 3299)/2 = (659108827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659108827:ℝ)/168755200)*ClassicalSixthBranch.v ((659108827:ℝ)/168755200)/ClassicalSixthBranch.r = (88160771911017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3298
  · change upperPayment 3299 ≤ upperValue ((point split endpoint 4096 3299+point split endpoint 4096 3300)/2)
    have hp : upperPayment 3299 = (121700558933:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3299+point split endpoint 4096 3300)/2 = (6399359:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6399359:ℝ)/1638400)*ClassicalSixthBranch.v ((6399359:ℝ)/1638400)/ClassicalSixthBranch.r = (855742058327:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3299
  · change upperPayment 3300 ≤ upperValue ((point split endpoint 4096 3300+point split endpoint 4096 3301)/2)
    have hp : upperPayment 3300 = (121562713440:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3300+point split endpoint 4096 3301)/2 = (659159127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659159127:ℝ)/168755200)*ClassicalSixthBranch.v ((659159127:ℝ)/168755200)/ClassicalSixthBranch.r = (88122094128417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3300
  · change upperPayment 3301 ≤ upperValue ((point split endpoint 4096 3301+point split endpoint 4096 3302)/2)
    have hp : upperPayment 3301 = (121424832886:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3301+point split endpoint 4096 3302)/2 = (659184277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659184277:ℝ)/168755200)*ClassicalSixthBranch.v ((659184277:ℝ)/168755200)/ClassicalSixthBranch.r = (88102758273225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3301
  · change upperPayment 3302 ≤ upperValue ((point split endpoint 4096 3302+point split endpoint 4096 3303)/2)
    have hp : upperPayment 3302 = (121286917262:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3302+point split endpoint 4096 3303)/2 = (659209427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659209427:ℝ)/168755200)*ClassicalSixthBranch.v ((659209427:ℝ)/168755200)/ClassicalSixthBranch.r = (88083424442105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3302
  · change upperPayment 3303 ≤ upperValue ((point split endpoint 4096 3303+point split endpoint 4096 3304)/2)
    have hp : upperPayment 3303 = (121148966559:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3303+point split endpoint 4096 3304)/2 = (659234577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659234577:ℝ)/168755200)*ClassicalSixthBranch.v ((659234577:ℝ)/168755200)/ClassicalSixthBranch.r = (88064092635057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3303
  · change upperPayment 3304 ≤ upperValue ((point split endpoint 4096 3304+point split endpoint 4096 3305)/2)
    have hp : upperPayment 3304 = (121010980769:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3304+point split endpoint 4096 3305)/2 = (659259727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659259727:ℝ)/168755200)*ClassicalSixthBranch.v ((659259727:ℝ)/168755200)/ClassicalSixthBranch.r = (88044762852081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3304
  · change upperPayment 3305 ≤ upperValue ((point split endpoint 4096 3305+point split endpoint 4096 3306)/2)
    have hp : upperPayment 3305 = (120872959883:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3305+point split endpoint 4096 3306)/2 = (659284877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659284877:ℝ)/168755200)*ClassicalSixthBranch.v ((659284877:ℝ)/168755200)/ClassicalSixthBranch.r = (88025435093177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3305
  · change upperPayment 3306 ≤ upperValue ((point split endpoint 4096 3306+point split endpoint 4096 3307)/2)
    have hp : upperPayment 3306 = (120734903892:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3306+point split endpoint 4096 3307)/2 = (659310027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659310027:ℝ)/168755200)*ClassicalSixthBranch.v ((659310027:ℝ)/168755200)/ClassicalSixthBranch.r = (88006109358345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3306
  · change upperPayment 3307 ≤ upperValue ((point split endpoint 4096 3307+point split endpoint 4096 3308)/2)
    have hp : upperPayment 3307 = (120596812788:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3307+point split endpoint 4096 3308)/2 = (659335177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659335177:ℝ)/168755200)*ClassicalSixthBranch.v ((659335177:ℝ)/168755200)/ClassicalSixthBranch.r = (87986785647585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3307
  · change upperPayment 3308 ≤ upperValue ((point split endpoint 4096 3308+point split endpoint 4096 3309)/2)
    have hp : upperPayment 3308 = (120458686561:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3308+point split endpoint 4096 3309)/2 = (659360327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659360327:ℝ)/168755200)*ClassicalSixthBranch.v ((659360327:ℝ)/168755200)/ClassicalSixthBranch.r = (87967463960897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3308
  · change upperPayment 3309 ≤ upperValue ((point split endpoint 4096 3309+point split endpoint 4096 3310)/2)
    have hp : upperPayment 3309 = (120320525202:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3309+point split endpoint 4096 3310)/2 = (659385477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659385477:ℝ)/168755200)*ClassicalSixthBranch.v ((659385477:ℝ)/168755200)/ClassicalSixthBranch.r = (87948144298281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3309
  · change upperPayment 3310 ≤ upperValue ((point split endpoint 4096 3310+point split endpoint 4096 3311)/2)
    have hp : upperPayment 3310 = (120182328704:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3310+point split endpoint 4096 3311)/2 = (659410627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659410627:ℝ)/168755200)*ClassicalSixthBranch.v ((659410627:ℝ)/168755200)/ClassicalSixthBranch.r = (87928826659737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3310
  · change upperPayment 3311 ≤ upperValue ((point split endpoint 4096 3311+point split endpoint 4096 3312)/2)
    have hp : upperPayment 3311 = (120044097057:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3311+point split endpoint 4096 3312)/2 = (659435777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659435777:ℝ)/168755200)*ClassicalSixthBranch.v ((659435777:ℝ)/168755200)/ClassicalSixthBranch.r = (87909511045265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3311
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_206
