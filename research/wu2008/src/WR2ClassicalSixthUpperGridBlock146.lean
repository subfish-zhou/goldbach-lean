import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints146
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_146 (j : Fin 16) : upperPayment (16*146+j.val) ≤
    upperValue ((point split endpoint 4096 (16*146+j.val)+point split endpoint 4096 (16*146+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2336 ≤ upperValue ((point split endpoint 4096 2336+point split endpoint 4096 2337)/2)
    have hp : upperPayment 2336 = (239358917098:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2336+point split endpoint 4096 2337)/2 = (634914527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634914527:ℝ)/168755200)*ClassicalSixthBranch.v ((634914527:ℝ)/168755200)/ClassicalSixthBranch.r = (107703315142865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2336
  · change upperPayment 2337 ≤ upperValue ((point split endpoint 4096 2337+point split endpoint 4096 2338)/2)
    have hp : upperPayment 2337 = (239251257432:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2337+point split endpoint 4096 2338)/2 = (634939677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634939677:ℝ)/168755200)*ClassicalSixthBranch.v ((634939677:ℝ)/168755200)/ClassicalSixthBranch.r = (107682028082265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2337
  · change upperPayment 2338 ≤ upperValue ((point split endpoint 4096 2338+point split endpoint 4096 2339)/2)
    have hp : upperPayment 2338 = (239143569678:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2338+point split endpoint 4096 2339)/2 = (634964827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634964827:ℝ)/168755200)*ClassicalSixthBranch.v ((634964827:ℝ)/168755200)/ClassicalSixthBranch.r = (107660743045737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2338
  · change upperPayment 2339 ≤ upperValue ((point split endpoint 4096 2339+point split endpoint 4096 2340)/2)
    have hp : upperPayment 2339 = (239035853829:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2339+point split endpoint 4096 2340)/2 = (634989977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634989977:ℝ)/168755200)*ClassicalSixthBranch.v ((634989977:ℝ)/168755200)/ClassicalSixthBranch.r = (107639460033281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2339
  · change upperPayment 2340 ≤ upperValue ((point split endpoint 4096 2340+point split endpoint 4096 2341)/2)
    have hp : upperPayment 2340 = (238928109879:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2340+point split endpoint 4096 2341)/2 = (635015127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635015127:ℝ)/168755200)*ClassicalSixthBranch.v ((635015127:ℝ)/168755200)/ClassicalSixthBranch.r = (107618179044897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2340
  · change upperPayment 2341 ≤ upperValue ((point split endpoint 4096 2341+point split endpoint 4096 2342)/2)
    have hp : upperPayment 2341 = (238820337823:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2341+point split endpoint 4096 2342)/2 = (635040277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635040277:ℝ)/168755200)*ClassicalSixthBranch.v ((635040277:ℝ)/168755200)/ClassicalSixthBranch.r = (107596900080585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2341
  · change upperPayment 2342 ≤ upperValue ((point split endpoint 4096 2342+point split endpoint 4096 2343)/2)
    have hp : upperPayment 2342 = (238712537655:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2342+point split endpoint 4096 2343)/2 = (635065427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635065427:ℝ)/168755200)*ClassicalSixthBranch.v ((635065427:ℝ)/168755200)/ClassicalSixthBranch.r = (107575623140345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2342
  · change upperPayment 2343 ≤ upperValue ((point split endpoint 4096 2343+point split endpoint 4096 2344)/2)
    have hp : upperPayment 2343 = (238604709368:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2343+point split endpoint 4096 2344)/2 = (635090577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635090577:ℝ)/168755200)*ClassicalSixthBranch.v ((635090577:ℝ)/168755200)/ClassicalSixthBranch.r = (107554348224177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2343
  · change upperPayment 2344 ≤ upperValue ((point split endpoint 4096 2344+point split endpoint 4096 2345)/2)
    have hp : upperPayment 2344 = (238496852957:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2344+point split endpoint 4096 2345)/2 = (635115727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635115727:ℝ)/168755200)*ClassicalSixthBranch.v ((635115727:ℝ)/168755200)/ClassicalSixthBranch.r = (107533075332081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2344
  · change upperPayment 2345 ≤ upperValue ((point split endpoint 4096 2345+point split endpoint 4096 2346)/2)
    have hp : upperPayment 2345 = (238388968416:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2345+point split endpoint 4096 2346)/2 = (635140877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635140877:ℝ)/168755200)*ClassicalSixthBranch.v ((635140877:ℝ)/168755200)/ClassicalSixthBranch.r = (107511804464057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2345
  · change upperPayment 2346 ≤ upperValue ((point split endpoint 4096 2346+point split endpoint 4096 2347)/2)
    have hp : upperPayment 2346 = (238281055739:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2346+point split endpoint 4096 2347)/2 = (635166027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635166027:ℝ)/168755200)*ClassicalSixthBranch.v ((635166027:ℝ)/168755200)/ClassicalSixthBranch.r = (107490535620105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2346
  · change upperPayment 2347 ≤ upperValue ((point split endpoint 4096 2347+point split endpoint 4096 2348)/2)
    have hp : upperPayment 2347 = (238173114920:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2347+point split endpoint 4096 2348)/2 = (635191177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635191177:ℝ)/168755200)*ClassicalSixthBranch.v ((635191177:ℝ)/168755200)/ClassicalSixthBranch.r = (107469268800225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2347
  · change upperPayment 2348 ≤ upperValue ((point split endpoint 4096 2348+point split endpoint 4096 2349)/2)
    have hp : upperPayment 2348 = (238065145953:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2348+point split endpoint 4096 2349)/2 = (635216327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635216327:ℝ)/168755200)*ClassicalSixthBranch.v ((635216327:ℝ)/168755200)/ClassicalSixthBranch.r = (107448004004417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2348
  · change upperPayment 2349 ≤ upperValue ((point split endpoint 4096 2349+point split endpoint 4096 2350)/2)
    have hp : upperPayment 2349 = (237957148832:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2349+point split endpoint 4096 2350)/2 = (635241477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635241477:ℝ)/168755200)*ClassicalSixthBranch.v ((635241477:ℝ)/168755200)/ClassicalSixthBranch.r = (107426741232681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2349
  · change upperPayment 2350 ≤ upperValue ((point split endpoint 4096 2350+point split endpoint 4096 2351)/2)
    have hp : upperPayment 2350 = (237849123551:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2350+point split endpoint 4096 2351)/2 = (635266627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635266627:ℝ)/168755200)*ClassicalSixthBranch.v ((635266627:ℝ)/168755200)/ClassicalSixthBranch.r = (107405480485017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2350
  · change upperPayment 2351 ≤ upperValue ((point split endpoint 4096 2351+point split endpoint 4096 2352)/2)
    have hp : upperPayment 2351 = (237741070104:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2351+point split endpoint 4096 2352)/2 = (635291777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((635291777:ℝ)/168755200)*ClassicalSixthBranch.v ((635291777:ℝ)/168755200)/ClassicalSixthBranch.r = (107384221761425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2351
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_146
