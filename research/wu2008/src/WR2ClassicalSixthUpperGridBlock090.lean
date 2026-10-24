import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints090
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_090 (j : Fin 16) : upperPayment (16*90+j.val) ≤
    upperValue ((point split endpoint 4096 (16*90+j.val)+point split endpoint 4096 (16*90+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1440 ≤ upperValue ((point split endpoint 4096 1440+point split endpoint 4096 1441)/2)
    have hp : upperPayment 1440 = (325187329356:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1440+point split endpoint 4096 1441)/2 = (612380127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612380127:ℝ)/168755200)*ClassicalSixthBranch.v ((612380127:ℝ)/168755200)/ClassicalSixthBranch.r = (127589906918097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1440
  · change upperPayment 1441 ≤ upperValue ((point split endpoint 4096 1441+point split endpoint 4096 1442)/2)
    have hp : upperPayment 1441 = (325102718133:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1441+point split endpoint 4096 1442)/2 = (612405277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612405277:ℝ)/168755200)*ClassicalSixthBranch.v ((612405277:ℝ)/168755200)/ClassicalSixthBranch.r = (127566806288985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1441
  · change upperPayment 1442 ≤ upperValue ((point split endpoint 4096 1442+point split endpoint 4096 1443)/2)
    have hp : upperPayment 1442 = (325018083275:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1442+point split endpoint 4096 1443)/2 = (612430427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612430427:ℝ)/168755200)*ClassicalSixthBranch.v ((612430427:ℝ)/168755200)/ClassicalSixthBranch.r = (127543707683945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1442
  · change upperPayment 1443 ≤ upperValue ((point split endpoint 4096 1443+point split endpoint 4096 1444)/2)
    have hp : upperPayment 1443 = (324933424781:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1443+point split endpoint 4096 1444)/2 = (612455577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612455577:ℝ)/168755200)*ClassicalSixthBranch.v ((612455577:ℝ)/168755200)/ClassicalSixthBranch.r = (127520611102977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1443
  · change upperPayment 1444 ≤ upperValue ((point split endpoint 4096 1444+point split endpoint 4096 1445)/2)
    have hp : upperPayment 1444 = (324848742645:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1444+point split endpoint 4096 1445)/2 = (612480727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612480727:ℝ)/168755200)*ClassicalSixthBranch.v ((612480727:ℝ)/168755200)/ClassicalSixthBranch.r = (127497516546081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1444
  · change upperPayment 1445 ≤ upperValue ((point split endpoint 4096 1445+point split endpoint 4096 1446)/2)
    have hp : upperPayment 1445 = (324764036863:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1445+point split endpoint 4096 1446)/2 = (5946659:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5946659:ℝ)/1638400)*ClassicalSixthBranch.v ((5946659:ℝ)/1638400)/ClassicalSixthBranch.r = (1237615767119:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1445
  · change upperPayment 1446 ≤ upperValue ((point split endpoint 4096 1446+point split endpoint 4096 1447)/2)
    have hp : upperPayment 1446 = (324679307432:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1446+point split endpoint 4096 1447)/2 = (612531027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612531027:ℝ)/168755200)*ClassicalSixthBranch.v ((612531027:ℝ)/168755200)/ClassicalSixthBranch.r = (127451333504505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1446
  · change upperPayment 1447 ≤ upperValue ((point split endpoint 4096 1447+point split endpoint 4096 1448)/2)
    have hp : upperPayment 1447 = (324594554347:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1447+point split endpoint 4096 1448)/2 = (612556177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612556177:ℝ)/168755200)*ClassicalSixthBranch.v ((612556177:ℝ)/168755200)/ClassicalSixthBranch.r = (127428245019825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1447
  · change upperPayment 1448 ≤ upperValue ((point split endpoint 4096 1448+point split endpoint 4096 1449)/2)
    have hp : upperPayment 1448 = (324509777604:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1448+point split endpoint 4096 1449)/2 = (612581327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612581327:ℝ)/168755200)*ClassicalSixthBranch.v ((612581327:ℝ)/168755200)/ClassicalSixthBranch.r = (127405158559217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1448
  · change upperPayment 1449 ≤ upperValue ((point split endpoint 4096 1449+point split endpoint 4096 1450)/2)
    have hp : upperPayment 1449 = (324424977199:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1449+point split endpoint 4096 1450)/2 = (612606477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612606477:ℝ)/168755200)*ClassicalSixthBranch.v ((612606477:ℝ)/168755200)/ClassicalSixthBranch.r = (127382074122681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1449
  · change upperPayment 1450 ≤ upperValue ((point split endpoint 4096 1450+point split endpoint 4096 1451)/2)
    have hp : upperPayment 1450 = (324340153128:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1450+point split endpoint 4096 1451)/2 = (612631627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612631627:ℝ)/168755200)*ClassicalSixthBranch.v ((612631627:ℝ)/168755200)/ClassicalSixthBranch.r = (127358991710217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1450
  · change upperPayment 1451 ≤ upperValue ((point split endpoint 4096 1451+point split endpoint 4096 1452)/2)
    have hp : upperPayment 1451 = (324255305386:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1451+point split endpoint 4096 1452)/2 = (612656777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612656777:ℝ)/168755200)*ClassicalSixthBranch.v ((612656777:ℝ)/168755200)/ClassicalSixthBranch.r = (127335911321825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1451
  · change upperPayment 1452 ≤ upperValue ((point split endpoint 4096 1452+point split endpoint 4096 1453)/2)
    have hp : upperPayment 1452 = (324170433970:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1452+point split endpoint 4096 1453)/2 = (612681927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612681927:ℝ)/168755200)*ClassicalSixthBranch.v ((612681927:ℝ)/168755200)/ClassicalSixthBranch.r = (127312832957505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1452
  · change upperPayment 1453 ≤ upperValue ((point split endpoint 4096 1453+point split endpoint 4096 1454)/2)
    have hp : upperPayment 1453 = (324085538875:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1453+point split endpoint 4096 1454)/2 = (612707077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612707077:ℝ)/168755200)*ClassicalSixthBranch.v ((612707077:ℝ)/168755200)/ClassicalSixthBranch.r = (127289756617257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1453
  · change upperPayment 1454 ≤ upperValue ((point split endpoint 4096 1454+point split endpoint 4096 1455)/2)
    have hp : upperPayment 1454 = (324000620098:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1454+point split endpoint 4096 1455)/2 = (612732227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612732227:ℝ)/168755200)*ClassicalSixthBranch.v ((612732227:ℝ)/168755200)/ClassicalSixthBranch.r = (127266682301081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1454
  · change upperPayment 1455 ≤ upperValue ((point split endpoint 4096 1455+point split endpoint 4096 1456)/2)
    have hp : upperPayment 1455 = (323915677634:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1455+point split endpoint 4096 1456)/2 = (612757377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((612757377:ℝ)/168755200)*ClassicalSixthBranch.v ((612757377:ℝ)/168755200)/ClassicalSixthBranch.r = (127243610008977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1455
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_090
