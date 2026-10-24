import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints087
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_087 (j : Fin 16) : upperPayment (16*87+j.val) ≤
    upperValue ((point split endpoint 4096 (16*87+j.val)+point split endpoint 4096 (16*87+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1392 ≤ upperValue ((point split endpoint 4096 1392+point split endpoint 4096 1393)/2)
    have hp : upperPayment 1392 = (329220955730:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1392+point split endpoint 4096 1393)/2 = (611172927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611172927:ℝ)/168755200)*ClassicalSixthBranch.v ((611172927:ℝ)/168755200)/ClassicalSixthBranch.r = (128701117424145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1392
  · change upperPayment 1393 ≤ upperValue ((point split endpoint 4096 1393+point split endpoint 4096 1394)/2)
    have hp : upperPayment 1393 = (329137474091:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1393+point split endpoint 4096 1394)/2 = (611198077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611198077:ℝ)/168755200)*ClassicalSixthBranch.v ((611198077:ℝ)/168755200)/ClassicalSixthBranch.r = (128677919639577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1393
  · change upperPayment 1394 ≤ upperValue ((point split endpoint 4096 1394+point split endpoint 4096 1395)/2)
    have hp : upperPayment 1394 = (329053969015:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1394+point split endpoint 4096 1395)/2 = (611223227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611223227:ℝ)/168755200)*ClassicalSixthBranch.v ((611223227:ℝ)/168755200)/ClassicalSixthBranch.r = (128654723879081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1394
  · change upperPayment 1395 ≤ upperValue ((point split endpoint 4096 1395+point split endpoint 4096 1396)/2)
    have hp : upperPayment 1395 = (328970440497:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1395+point split endpoint 4096 1396)/2 = (611248377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611248377:ℝ)/168755200)*ClassicalSixthBranch.v ((611248377:ℝ)/168755200)/ClassicalSixthBranch.r = (128631530142657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1395
  · change upperPayment 1396 ≤ upperValue ((point split endpoint 4096 1396+point split endpoint 4096 1397)/2)
    have hp : upperPayment 1396 = (328886888533:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1396+point split endpoint 4096 1397)/2 = (611273527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611273527:ℝ)/168755200)*ClassicalSixthBranch.v ((611273527:ℝ)/168755200)/ClassicalSixthBranch.r = (128608338430305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1396
  · change upperPayment 1397 ≤ upperValue ((point split endpoint 4096 1397+point split endpoint 4096 1398)/2)
    have hp : upperPayment 1397 = (328803313120:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1397+point split endpoint 4096 1398)/2 = (611298677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611298677:ℝ)/168755200)*ClassicalSixthBranch.v ((611298677:ℝ)/168755200)/ClassicalSixthBranch.r = (128585148742025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1397
  · change upperPayment 1398 ≤ upperValue ((point split endpoint 4096 1398+point split endpoint 4096 1399)/2)
    have hp : upperPayment 1398 = (328719714252:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1398+point split endpoint 4096 1399)/2 = (611323827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611323827:ℝ)/168755200)*ClassicalSixthBranch.v ((611323827:ℝ)/168755200)/ClassicalSixthBranch.r = (128561961077817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1398
  · change upperPayment 1399 ≤ upperValue ((point split endpoint 4096 1399+point split endpoint 4096 1400)/2)
    have hp : upperPayment 1399 = (328636091928:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1399+point split endpoint 4096 1400)/2 = (611348977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611348977:ℝ)/168755200)*ClassicalSixthBranch.v ((611348977:ℝ)/168755200)/ClassicalSixthBranch.r = (128538775437681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1399
  · change upperPayment 1400 ≤ upperValue ((point split endpoint 4096 1400+point split endpoint 4096 1401)/2)
    have hp : upperPayment 1400 = (328552446141:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1400+point split endpoint 4096 1401)/2 = (611374127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611374127:ℝ)/168755200)*ClassicalSixthBranch.v ((611374127:ℝ)/168755200)/ClassicalSixthBranch.r = (128515591821617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1400
  · change upperPayment 1401 ≤ upperValue ((point split endpoint 4096 1401+point split endpoint 4096 1402)/2)
    have hp : upperPayment 1401 = (328468776889:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1401+point split endpoint 4096 1402)/2 = (611399277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611399277:ℝ)/168755200)*ClassicalSixthBranch.v ((611399277:ℝ)/168755200)/ClassicalSixthBranch.r = (128492410229625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1401
  · change upperPayment 1402 ≤ upperValue ((point split endpoint 4096 1402+point split endpoint 4096 1403)/2)
    have hp : upperPayment 1402 = (328385084166:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1402+point split endpoint 4096 1403)/2 = (611424427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611424427:ℝ)/168755200)*ClassicalSixthBranch.v ((611424427:ℝ)/168755200)/ClassicalSixthBranch.r = (128469230661705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1402
  · change upperPayment 1403 ≤ upperValue ((point split endpoint 4096 1403+point split endpoint 4096 1404)/2)
    have hp : upperPayment 1403 = (328301367970:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1403+point split endpoint 4096 1404)/2 = (611449577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611449577:ℝ)/168755200)*ClassicalSixthBranch.v ((611449577:ℝ)/168755200)/ClassicalSixthBranch.r = (128446053117857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1403
  · change upperPayment 1404 ≤ upperValue ((point split endpoint 4096 1404+point split endpoint 4096 1405)/2)
    have hp : upperPayment 1404 = (328217628296:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1404+point split endpoint 4096 1405)/2 = (611474727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611474727:ℝ)/168755200)*ClassicalSixthBranch.v ((611474727:ℝ)/168755200)/ClassicalSixthBranch.r = (128422877598081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1404
  · change upperPayment 1405 ≤ upperValue ((point split endpoint 4096 1405+point split endpoint 4096 1406)/2)
    have hp : upperPayment 1405 = (328133865139:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1405+point split endpoint 4096 1406)/2 = (611499877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611499877:ℝ)/168755200)*ClassicalSixthBranch.v ((611499877:ℝ)/168755200)/ClassicalSixthBranch.r = (128399704102377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1405
  · change upperPayment 1406 ≤ upperValue ((point split endpoint 4096 1406+point split endpoint 4096 1407)/2)
    have hp : upperPayment 1406 = (328050078497:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1406+point split endpoint 4096 1407)/2 = (611525027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611525027:ℝ)/168755200)*ClassicalSixthBranch.v ((611525027:ℝ)/168755200)/ClassicalSixthBranch.r = (128376532630745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1406
  · change upperPayment 1407 ≤ upperValue ((point split endpoint 4096 1407+point split endpoint 4096 1408)/2)
    have hp : upperPayment 1407 = (327966268364:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1407+point split endpoint 4096 1408)/2 = (611550177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611550177:ℝ)/168755200)*ClassicalSixthBranch.v ((611550177:ℝ)/168755200)/ClassicalSixthBranch.r = (128353363183185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1407
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_087
