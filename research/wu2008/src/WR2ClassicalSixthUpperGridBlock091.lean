import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints091
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_091 (j : Fin 16) : upperPayment (16*91+j.val) ≤
    upperValue ((point split endpoint 4096 (16*91+j.val)+point split endpoint 4096 (16*91+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1456 ≤ upperValue ((point split endpoint 4096 1456+point split endpoint 4096 1457)/2)
    have hp : upperPayment 1456 = (323830711478:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1456+point split endpoint 4096 1457)/2 = (612782527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612782527:ℝ)/168755200)*ClassicalSixthBranch.v ((612782527:ℝ)/168755200)/ClassicalSixthBranch.r = (127220539740945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1456
  · change upperPayment 1457 ≤ upperValue ((point split endpoint 4096 1457+point split endpoint 4096 1458)/2)
    have hp : upperPayment 1457 = (323745721628:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1457+point split endpoint 4096 1458)/2 = (612807677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612807677:ℝ)/168755200)*ClassicalSixthBranch.v ((612807677:ℝ)/168755200)/ClassicalSixthBranch.r = (127197471496985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1457
  · change upperPayment 1458 ≤ upperValue ((point split endpoint 4096 1458+point split endpoint 4096 1459)/2)
    have hp : upperPayment 1458 = (323660708078:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1458+point split endpoint 4096 1459)/2 = (612832827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612832827:ℝ)/168755200)*ClassicalSixthBranch.v ((612832827:ℝ)/168755200)/ClassicalSixthBranch.r = (127174405277097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1458
  · change upperPayment 1459 ≤ upperValue ((point split endpoint 4096 1459+point split endpoint 4096 1460)/2)
    have hp : upperPayment 1459 = (323575670825:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1459+point split endpoint 4096 1460)/2 = (612857977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612857977:ℝ)/168755200)*ClassicalSixthBranch.v ((612857977:ℝ)/168755200)/ClassicalSixthBranch.r = (127151341081281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1459
  · change upperPayment 1460 ≤ upperValue ((point split endpoint 4096 1460+point split endpoint 4096 1461)/2)
    have hp : upperPayment 1460 = (323490609864:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1460+point split endpoint 4096 1461)/2 = (612883127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612883127:ℝ)/168755200)*ClassicalSixthBranch.v ((612883127:ℝ)/168755200)/ClassicalSixthBranch.r = (127128278909537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1460
  · change upperPayment 1461 ≤ upperValue ((point split endpoint 4096 1461+point split endpoint 4096 1462)/2)
    have hp : upperPayment 1461 = (323405525191:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1461+point split endpoint 4096 1462)/2 = (612908277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612908277:ℝ)/168755200)*ClassicalSixthBranch.v ((612908277:ℝ)/168755200)/ClassicalSixthBranch.r = (127105218761865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1461
  · change upperPayment 1462 ≤ upperValue ((point split endpoint 4096 1462+point split endpoint 4096 1463)/2)
    have hp : upperPayment 1462 = (323320416803:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1462+point split endpoint 4096 1463)/2 = (612933427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612933427:ℝ)/168755200)*ClassicalSixthBranch.v ((612933427:ℝ)/168755200)/ClassicalSixthBranch.r = (127082160638265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1462
  · change upperPayment 1463 ≤ upperValue ((point split endpoint 4096 1463+point split endpoint 4096 1464)/2)
    have hp : upperPayment 1463 = (323235284694:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1463+point split endpoint 4096 1464)/2 = (612958577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612958577:ℝ)/168755200)*ClassicalSixthBranch.v ((612958577:ℝ)/168755200)/ClassicalSixthBranch.r = (127059104538737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1463
  · change upperPayment 1464 ≤ upperValue ((point split endpoint 4096 1464+point split endpoint 4096 1465)/2)
    have hp : upperPayment 1464 = (323150128861:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1464+point split endpoint 4096 1465)/2 = (612983727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612983727:ℝ)/168755200)*ClassicalSixthBranch.v ((612983727:ℝ)/168755200)/ClassicalSixthBranch.r = (127036050463281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1464
  · change upperPayment 1465 ≤ upperValue ((point split endpoint 4096 1465+point split endpoint 4096 1466)/2)
    have hp : upperPayment 1465 = (323064949300:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1465+point split endpoint 4096 1466)/2 = (613008877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613008877:ℝ)/168755200)*ClassicalSixthBranch.v ((613008877:ℝ)/168755200)/ClassicalSixthBranch.r = (127012998411897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1465
  · change upperPayment 1466 ≤ upperValue ((point split endpoint 4096 1466+point split endpoint 4096 1467)/2)
    have hp : upperPayment 1466 = (322979746006:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1466+point split endpoint 4096 1467)/2 = (613034027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613034027:ℝ)/168755200)*ClassicalSixthBranch.v ((613034027:ℝ)/168755200)/ClassicalSixthBranch.r = (126989948384585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1466
  · change upperPayment 1467 ≤ upperValue ((point split endpoint 4096 1467+point split endpoint 4096 1468)/2)
    have hp : upperPayment 1467 = (322894518976:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1467+point split endpoint 4096 1468)/2 = (613059177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613059177:ℝ)/168755200)*ClassicalSixthBranch.v ((613059177:ℝ)/168755200)/ClassicalSixthBranch.r = (126966900381345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1467
  · change upperPayment 1468 ≤ upperValue ((point split endpoint 4096 1468+point split endpoint 4096 1469)/2)
    have hp : upperPayment 1468 = (322809268205:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1468+point split endpoint 4096 1469)/2 = (613084327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613084327:ℝ)/168755200)*ClassicalSixthBranch.v ((613084327:ℝ)/168755200)/ClassicalSixthBranch.r = (126943854402177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1468
  · change upperPayment 1469 ≤ upperValue ((point split endpoint 4096 1469+point split endpoint 4096 1470)/2)
    have hp : upperPayment 1469 = (322723993688:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1469+point split endpoint 4096 1470)/2 = (613109477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613109477:ℝ)/168755200)*ClassicalSixthBranch.v ((613109477:ℝ)/168755200)/ClassicalSixthBranch.r = (1232240878127:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1469
  · change upperPayment 1470 ≤ upperValue ((point split endpoint 4096 1470+point split endpoint 4096 1471)/2)
    have hp : upperPayment 1470 = (322638695423:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1470+point split endpoint 4096 1471)/2 = (613134627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613134627:ℝ)/168755200)*ClassicalSixthBranch.v ((613134627:ℝ)/168755200)/ClassicalSixthBranch.r = (126897768516057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1470
  · change upperPayment 1471 ≤ upperValue ((point split endpoint 4096 1471+point split endpoint 4096 1472)/2)
    have hp : upperPayment 1471 = (322553373404:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1471+point split endpoint 4096 1472)/2 = (613159777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((613159777:ℝ)/168755200)*ClassicalSixthBranch.v ((613159777:ℝ)/168755200)/ClassicalSixthBranch.r = (126874728609105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1471
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_091
