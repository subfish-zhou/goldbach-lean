import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints086
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_086 (j : Fin 16) : upperPayment (16*86+j.val) ≤
    upperValue ((point split endpoint 4096 (16*86+j.val)+point split endpoint 4096 (16*86+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1376 ≤ upperValue ((point split endpoint 4096 1376+point split endpoint 4096 1377)/2)
    have hp : upperPayment 1376 = (330553477731:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1376+point split endpoint 4096 1377)/2 = (610770527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610770527:ℝ)/168755200)*ClassicalSixthBranch.v ((610770527:ℝ)/168755200)/ClassicalSixthBranch.r = (129072557251025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1376
  · change upperPayment 1377 ≤ upperValue ((point split endpoint 4096 1377+point split endpoint 4096 1378)/2)
    have hp : upperPayment 1377 = (330470370546:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1377+point split endpoint 4096 1378)/2 = (610795677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610795677:ℝ)/168755200)*ClassicalSixthBranch.v ((610795677:ℝ)/168755200)/ClassicalSixthBranch.r = (129049327081305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1377
  · change upperPayment 1378 ≤ upperValue ((point split endpoint 4096 1378+point split endpoint 4096 1379)/2)
    have hp : upperPayment 1378 = (330387239987:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1378+point split endpoint 4096 1379)/2 = (610820827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610820827:ℝ)/168755200)*ClassicalSixthBranch.v ((610820827:ℝ)/168755200)/ClassicalSixthBranch.r = (129026098935657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1378
  · change upperPayment 1379 ≤ upperValue ((point split endpoint 4096 1379+point split endpoint 4096 1380)/2)
    have hp : upperPayment 1379 = (330304086051:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1379+point split endpoint 4096 1380)/2 = (610845977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610845977:ℝ)/168755200)*ClassicalSixthBranch.v ((610845977:ℝ)/168755200)/ClassicalSixthBranch.r = (129002872814081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1379
  · change upperPayment 1380 ≤ upperValue ((point split endpoint 4096 1380+point split endpoint 4096 1381)/2)
    have hp : upperPayment 1380 = (330220908734:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1380+point split endpoint 4096 1381)/2 = (610871127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610871127:ℝ)/168755200)*ClassicalSixthBranch.v ((610871127:ℝ)/168755200)/ClassicalSixthBranch.r = (128979648716577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1380
  · change upperPayment 1381 ≤ upperValue ((point split endpoint 4096 1381+point split endpoint 4096 1382)/2)
    have hp : upperPayment 1381 = (330137708032:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1381+point split endpoint 4096 1382)/2 = (610896277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610896277:ℝ)/168755200)*ClassicalSixthBranch.v ((610896277:ℝ)/168755200)/ClassicalSixthBranch.r = (128956426643145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1381
  · change upperPayment 1382 ≤ upperValue ((point split endpoint 4096 1382+point split endpoint 4096 1383)/2)
    have hp : upperPayment 1382 = (330054483940:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1382+point split endpoint 4096 1383)/2 = (610921427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610921427:ℝ)/168755200)*ClassicalSixthBranch.v ((610921427:ℝ)/168755200)/ClassicalSixthBranch.r = (128933206593785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1382
  · change upperPayment 1383 ≤ upperValue ((point split endpoint 4096 1383+point split endpoint 4096 1384)/2)
    have hp : upperPayment 1383 = (329971236455:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1383+point split endpoint 4096 1384)/2 = (610946577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610946577:ℝ)/168755200)*ClassicalSixthBranch.v ((610946577:ℝ)/168755200)/ClassicalSixthBranch.r = (128909988568497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1383
  · change upperPayment 1384 ≤ upperValue ((point split endpoint 4096 1384+point split endpoint 4096 1385)/2)
    have hp : upperPayment 1384 = (329887965573:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1384+point split endpoint 4096 1385)/2 = (610971727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610971727:ℝ)/168755200)*ClassicalSixthBranch.v ((610971727:ℝ)/168755200)/ClassicalSixthBranch.r = (128886772567281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1384
  · change upperPayment 1385 ≤ upperValue ((point split endpoint 4096 1385+point split endpoint 4096 1386)/2)
    have hp : upperPayment 1385 = (329804671289:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1385+point split endpoint 4096 1386)/2 = (610996877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((610996877:ℝ)/168755200)*ClassicalSixthBranch.v ((610996877:ℝ)/168755200)/ClassicalSixthBranch.r = (128863558590137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1385
  · change upperPayment 1386 ≤ upperValue ((point split endpoint 4096 1386+point split endpoint 4096 1387)/2)
    have hp : upperPayment 1386 = (329721353600:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1386+point split endpoint 4096 1387)/2 = (611022027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611022027:ℝ)/168755200)*ClassicalSixthBranch.v ((611022027:ℝ)/168755200)/ClassicalSixthBranch.r = (128840346637065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1386
  · change upperPayment 1387 ≤ upperValue ((point split endpoint 4096 1387+point split endpoint 4096 1388)/2)
    have hp : upperPayment 1387 = (329638012502:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1387+point split endpoint 4096 1388)/2 = (611047177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611047177:ℝ)/168755200)*ClassicalSixthBranch.v ((611047177:ℝ)/168755200)/ClassicalSixthBranch.r = (128817136708065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1387
  · change upperPayment 1388 ≤ upperValue ((point split endpoint 4096 1388+point split endpoint 4096 1389)/2)
    have hp : upperPayment 1388 = (329554647991:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1388+point split endpoint 4096 1389)/2 = (611072327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611072327:ℝ)/168755200)*ClassicalSixthBranch.v ((611072327:ℝ)/168755200)/ClassicalSixthBranch.r = (128793928803137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1388
  · change upperPayment 1389 ≤ upperValue ((point split endpoint 4096 1389+point split endpoint 4096 1390)/2)
    have hp : upperPayment 1389 = (329471260062:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1389+point split endpoint 4096 1390)/2 = (611097477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611097477:ℝ)/168755200)*ClassicalSixthBranch.v ((611097477:ℝ)/168755200)/ClassicalSixthBranch.r = (128770722922281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1389
  · change upperPayment 1390 ≤ upperValue ((point split endpoint 4096 1390+point split endpoint 4096 1391)/2)
    have hp : upperPayment 1390 = (329387848711:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1390+point split endpoint 4096 1391)/2 = (611122627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611122627:ℝ)/168755200)*ClassicalSixthBranch.v ((611122627:ℝ)/168755200)/ClassicalSixthBranch.r = (128747519065497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1390
  · change upperPayment 1391 ≤ upperValue ((point split endpoint 4096 1391+point split endpoint 4096 1392)/2)
    have hp : upperPayment 1391 = (329304413935:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1391+point split endpoint 4096 1392)/2 = (611147777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((611147777:ℝ)/168755200)*ClassicalSixthBranch.v ((611147777:ℝ)/168755200)/ClassicalSixthBranch.r = (128724317232785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1391
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_086
