import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints089
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_089 (j : Fin 16) : upperPayment (16*89+j.val) ≤
    upperValue ((point split endpoint 4096 (16*89+j.val)+point split endpoint 4096 (16*89+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1424 ≤ upperValue ((point split endpoint 4096 1424+point split endpoint 4096 1425)/2)
    have hp : upperPayment 1424 = (326537898176:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1424+point split endpoint 4096 1425)/2 = (611977727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611977727:ℝ)/168755200)*ClassicalSixthBranch.v ((611977727:ℝ)/168755200)/ClassicalSixthBranch.r = (127959792257681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1424
  · change upperPayment 1425 ≤ upperValue ((point split endpoint 4096 1425+point split endpoint 4096 1426)/2)
    have hp : upperPayment 1425 = (326453664525:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1425+point split endpoint 4096 1426)/2 = (612002877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612002877:ℝ)/168755200)*ClassicalSixthBranch.v ((612002877:ℝ)/168755200)/ClassicalSixthBranch.r = (127936659243417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1425
  · change upperPayment 1426 ≤ upperValue ((point split endpoint 4096 1426+point split endpoint 4096 1427)/2)
    have hp : upperPayment 1426 = (326369407306:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1426+point split endpoint 4096 1427)/2 = (612028027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612028027:ℝ)/168755200)*ClassicalSixthBranch.v ((612028027:ℝ)/168755200)/ClassicalSixthBranch.r = (127913528253225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1426
  · change upperPayment 1427 ≤ upperValue ((point split endpoint 4096 1427+point split endpoint 4096 1428)/2)
    have hp : upperPayment 1427 = (326285126516:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1427+point split endpoint 4096 1428)/2 = (612053177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612053177:ℝ)/168755200)*ClassicalSixthBranch.v ((612053177:ℝ)/168755200)/ClassicalSixthBranch.r = (127890399287105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1427
  · change upperPayment 1428 ≤ upperValue ((point split endpoint 4096 1428+point split endpoint 4096 1429)/2)
    have hp : upperPayment 1428 = (326200822150:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1428+point split endpoint 4096 1429)/2 = (612078327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612078327:ℝ)/168755200)*ClassicalSixthBranch.v ((612078327:ℝ)/168755200)/ClassicalSixthBranch.r = (127867272345057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1428
  · change upperPayment 1429 ≤ upperValue ((point split endpoint 4096 1429+point split endpoint 4096 1430)/2)
    have hp : upperPayment 1429 = (326116494204:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1429+point split endpoint 4096 1430)/2 = (612103477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612103477:ℝ)/168755200)*ClassicalSixthBranch.v ((612103477:ℝ)/168755200)/ClassicalSixthBranch.r = (127844147427081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1429
  · change upperPayment 1430 ≤ upperValue ((point split endpoint 4096 1430+point split endpoint 4096 1431)/2)
    have hp : upperPayment 1430 = (326032142674:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1430+point split endpoint 4096 1431)/2 = (612128627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612128627:ℝ)/168755200)*ClassicalSixthBranch.v ((612128627:ℝ)/168755200)/ClassicalSixthBranch.r = (127821024533177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1430
  · change upperPayment 1431 ≤ upperValue ((point split endpoint 4096 1431+point split endpoint 4096 1432)/2)
    have hp : upperPayment 1431 = (325947767556:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1431+point split endpoint 4096 1432)/2 = (612153777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612153777:ℝ)/168755200)*ClassicalSixthBranch.v ((612153777:ℝ)/168755200)/ClassicalSixthBranch.r = (127797903663345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1431
  · change upperPayment 1432 ≤ upperValue ((point split endpoint 4096 1432+point split endpoint 4096 1433)/2)
    have hp : upperPayment 1432 = (325863368846:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1432+point split endpoint 4096 1433)/2 = (612178927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612178927:ℝ)/168755200)*ClassicalSixthBranch.v ((612178927:ℝ)/168755200)/ClassicalSixthBranch.r = (127774784817585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1432
  · change upperPayment 1433 ≤ upperValue ((point split endpoint 4096 1433+point split endpoint 4096 1434)/2)
    have hp : upperPayment 1433 = (325778946540:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1433+point split endpoint 4096 1434)/2 = (612204077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612204077:ℝ)/168755200)*ClassicalSixthBranch.v ((612204077:ℝ)/168755200)/ClassicalSixthBranch.r = (127751667995897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1433
  · change upperPayment 1434 ≤ upperValue ((point split endpoint 4096 1434+point split endpoint 4096 1435)/2)
    have hp : upperPayment 1434 = (325694500633:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1434+point split endpoint 4096 1435)/2 = (612229227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612229227:ℝ)/168755200)*ClassicalSixthBranch.v ((612229227:ℝ)/168755200)/ClassicalSixthBranch.r = (127728553198281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1434
  · change upperPayment 1435 ≤ upperValue ((point split endpoint 4096 1435+point split endpoint 4096 1436)/2)
    have hp : upperPayment 1435 = (325610031122:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1435+point split endpoint 4096 1436)/2 = (612254377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612254377:ℝ)/168755200)*ClassicalSixthBranch.v ((612254377:ℝ)/168755200)/ClassicalSixthBranch.r = (127705440424737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1435
  · change upperPayment 1436 ≤ upperValue ((point split endpoint 4096 1436+point split endpoint 4096 1437)/2)
    have hp : upperPayment 1436 = (325525538002:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1436+point split endpoint 4096 1437)/2 = (612279527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612279527:ℝ)/168755200)*ClassicalSixthBranch.v ((612279527:ℝ)/168755200)/ClassicalSixthBranch.r = (127682329675265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1436
  · change upperPayment 1437 ≤ upperValue ((point split endpoint 4096 1437+point split endpoint 4096 1438)/2)
    have hp : upperPayment 1437 = (325441021270:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1437+point split endpoint 4096 1438)/2 = (612304677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612304677:ℝ)/168755200)*ClassicalSixthBranch.v ((612304677:ℝ)/168755200)/ClassicalSixthBranch.r = (127659220949865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1437
  · change upperPayment 1438 ≤ upperValue ((point split endpoint 4096 1438+point split endpoint 4096 1439)/2)
    have hp : upperPayment 1438 = (325356480921:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1438+point split endpoint 4096 1439)/2 = (612329827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612329827:ℝ)/168755200)*ClassicalSixthBranch.v ((612329827:ℝ)/168755200)/ClassicalSixthBranch.r = (127636114248537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1438
  · change upperPayment 1439 ≤ upperValue ((point split endpoint 4096 1439+point split endpoint 4096 1440)/2)
    have hp : upperPayment 1439 = (325271916951:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1439+point split endpoint 4096 1440)/2 = (612354977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612354977:ℝ)/168755200)*ClassicalSixthBranch.v ((612354977:ℝ)/168755200)/ClassicalSixthBranch.r = (127613009571281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1439
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_089
