import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints025
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_025 (j : Fin 16) : upperPayment (16*25+j.val) ≤
    upperValue ((point split endpoint 4096 (16*25+j.val)+point split endpoint 4096 (16*25+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 400 ≤ upperValue ((point split endpoint 4096 400+point split endpoint 4096 401)/2)
    have hp : upperPayment 400 = (401085309211:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 400+point split endpoint 4096 401)/2 = (586224127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586224127:ℝ)/168755200)*ClassicalSixthBranch.v ((586224127:ℝ)/168755200)/ClassicalSixthBranch.r = (152710231849617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_400
  · change upperPayment 401 ≤ upperValue ((point split endpoint 4096 401+point split endpoint 4096 402)/2)
    have hp : upperPayment 401 = (401023345062:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 401+point split endpoint 4096 402)/2 = (586249277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586249277:ℝ)/168755200)*ClassicalSixthBranch.v ((586249277:ℝ)/168755200)/ClassicalSixthBranch.r = (152685026185625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_401
  · change upperPayment 402 ≤ upperValue ((point split endpoint 4096 402+point split endpoint 4096 403)/2)
    have hp : upperPayment 402 = (400961360727:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 402+point split endpoint 4096 403)/2 = (586274427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586274427:ℝ)/168755200)*ClassicalSixthBranch.v ((586274427:ℝ)/168755200)/ClassicalSixthBranch.r = (152659822545705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_402
  · change upperPayment 403 ≤ upperValue ((point split endpoint 4096 403+point split endpoint 4096 404)/2)
    have hp : upperPayment 403 = (400899356202:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 403+point split endpoint 4096 404)/2 = (586299577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586299577:ℝ)/168755200)*ClassicalSixthBranch.v ((586299577:ℝ)/168755200)/ClassicalSixthBranch.r = (152634620929857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_403
  · change upperPayment 404 ≤ upperValue ((point split endpoint 4096 404+point split endpoint 4096 405)/2)
    have hp : upperPayment 404 = (400837331486:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 404+point split endpoint 4096 405)/2 = (586324727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586324727:ℝ)/168755200)*ClassicalSixthBranch.v ((586324727:ℝ)/168755200)/ClassicalSixthBranch.r = (152609421338081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_404
  · change upperPayment 405 ≤ upperValue ((point split endpoint 4096 405+point split endpoint 4096 406)/2)
    have hp : upperPayment 405 = (400775286576:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 405+point split endpoint 4096 406)/2 = (586349877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586349877:ℝ)/168755200)*ClassicalSixthBranch.v ((586349877:ℝ)/168755200)/ClassicalSixthBranch.r = (152584223770377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_405
  · change upperPayment 406 ≤ upperValue ((point split endpoint 4096 406+point split endpoint 4096 407)/2)
    have hp : upperPayment 406 = (400713221470:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 406+point split endpoint 4096 407)/2 = (586375027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586375027:ℝ)/168755200)*ClassicalSixthBranch.v ((586375027:ℝ)/168755200)/ClassicalSixthBranch.r = (152559028226745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_406
  · change upperPayment 407 ≤ upperValue ((point split endpoint 4096 407+point split endpoint 4096 408)/2)
    have hp : upperPayment 407 = (400651136164:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 407+point split endpoint 4096 408)/2 = (586400177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586400177:ℝ)/168755200)*ClassicalSixthBranch.v ((586400177:ℝ)/168755200)/ClassicalSixthBranch.r = (152533834707185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_407
  · change upperPayment 408 ≤ upperValue ((point split endpoint 4096 408+point split endpoint 4096 409)/2)
    have hp : upperPayment 408 = (400589030656:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 408+point split endpoint 4096 409)/2 = (586425327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586425327:ℝ)/168755200)*ClassicalSixthBranch.v ((586425327:ℝ)/168755200)/ClassicalSixthBranch.r = (152508643211697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_408
  · change upperPayment 409 ≤ upperValue ((point split endpoint 4096 409+point split endpoint 4096 410)/2)
    have hp : upperPayment 409 = (400526904944:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 409+point split endpoint 4096 410)/2 = (586450477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586450477:ℝ)/168755200)*ClassicalSixthBranch.v ((586450477:ℝ)/168755200)/ClassicalSixthBranch.r = (152483453740281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_409
  · change upperPayment 410 ≤ upperValue ((point split endpoint 4096 410+point split endpoint 4096 411)/2)
    have hp : upperPayment 410 = (400464759024:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 410+point split endpoint 4096 411)/2 = (586475627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586475627:ℝ)/168755200)*ClassicalSixthBranch.v ((586475627:ℝ)/168755200)/ClassicalSixthBranch.r = (152458266292937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_410
  · change upperPayment 411 ≤ upperValue ((point split endpoint 4096 411+point split endpoint 4096 412)/2)
    have hp : upperPayment 411 = (400402592896:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 411+point split endpoint 4096 412)/2 = (586500777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586500777:ℝ)/168755200)*ClassicalSixthBranch.v ((586500777:ℝ)/168755200)/ClassicalSixthBranch.r = (152433080869665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_411
  · change upperPayment 412 ≤ upperValue ((point split endpoint 4096 412+point split endpoint 4096 413)/2)
    have hp : upperPayment 412 = (400340406554:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 412+point split endpoint 4096 413)/2 = (586525927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586525927:ℝ)/168755200)*ClassicalSixthBranch.v ((586525927:ℝ)/168755200)/ClassicalSixthBranch.r = (152407897470465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_412
  · change upperPayment 413 ≤ upperValue ((point split endpoint 4096 413+point split endpoint 4096 414)/2)
    have hp : upperPayment 413 = (400278199998:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 413+point split endpoint 4096 414)/2 = (586551077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586551077:ℝ)/168755200)*ClassicalSixthBranch.v ((586551077:ℝ)/168755200)/ClassicalSixthBranch.r = (152382716095337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_413
  · change upperPayment 414 ≤ upperValue ((point split endpoint 4096 414+point split endpoint 4096 415)/2)
    have hp : upperPayment 414 = (400215973225:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 414+point split endpoint 4096 415)/2 = (586576227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((586576227:ℝ)/168755200)*ClassicalSixthBranch.v ((586576227:ℝ)/168755200)/ClassicalSixthBranch.r = (152357536744281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_414
  · change upperPayment 415 ≤ upperValue ((point split endpoint 4096 415+point split endpoint 4096 416)/2)
    have hp : upperPayment 415 = (400153726231:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 415+point split endpoint 4096 416)/2 = (5695159:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5695159:ℝ)/1638400)*ClassicalSixthBranch.v ((5695159:ℝ)/1638400)/ClassicalSixthBranch.r = (1478954945799:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_415
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_025
