import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints090
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_090 (j : Fin 16) : lowerPayment (16*90+j.val) ≤
    lowerValue ((point 2 split 4096 (16*90+j.val)+point 2 split 4096 (16*90+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1440 ≤ lowerValue ((point 2 split 4096 1440+point 2 split 4096 1441)/2)
    have hp : lowerPayment 1440 = (179594775073:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1440+point 2 split 4096 1441)/2 = (421436811:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421436811:ℝ)/168755200)/ClassicalSixthBranch.v ((421436811:ℝ)/168755200) = (702644829307:ℝ)/351423096984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1440
  · change lowerPayment 1441 ≤ lowerValue ((point 2 split 4096 1441+point 2 split 4096 1442)/2)
    have hp : lowerPayment 1441 = (179694391811:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1441+point 2 split 4096 1442)/2 = (421495073:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421495073:ℝ)/168755200)/ClassicalSixthBranch.v ((421495073:ℝ)/168755200) = (702567515633:ℝ)/351375089096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1441
  · change lowerPayment 1442 ≤ lowerValue ((point 2 split 4096 1442+point 2 split 4096 1443)/2)
    have hp : lowerPayment 1442 = (179793987710:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1442+point 2 split 4096 1443)/2 = (84310667:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84310667:ℝ)/33751040)/ClassicalSixthBranch.v ((84310667:ℝ)/33751040) = (702490201959:ℝ)/351327081208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1442
  · change lowerPayment 1443 ≤ lowerValue ((point 2 split 4096 1443+point 2 split 4096 1444)/2)
    have hp : lowerPayment 1443 = (179893562793:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1443+point 2 split 4096 1444)/2 = (421611597:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421611597:ℝ)/168755200)/ClassicalSixthBranch.v ((421611597:ℝ)/168755200) = (140482577657:ℝ)/70255814664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1443
  · change lowerPayment 1444 ≤ lowerValue ((point 2 split 4096 1444+point 2 split 4096 1445)/2)
    have hp : lowerPayment 1444 = (179993117080:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1444+point 2 split 4096 1445)/2 = (421669859:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421669859:ℝ)/168755200)/ClassicalSixthBranch.v ((421669859:ℝ)/168755200) = (702335574611:ℝ)/351231065432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1444
  · change lowerPayment 1445 ≤ lowerValue ((point 2 split 4096 1445+point 2 split 4096 1446)/2)
    have hp : lowerPayment 1445 = (180092650596:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1445+point 2 split 4096 1446)/2 = (421728121:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421728121:ℝ)/168755200)/ClassicalSixthBranch.v ((421728121:ℝ)/168755200) = (702258260937:ℝ)/351183057544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1445
  · change lowerPayment 1446 ≤ lowerValue ((point 2 split 4096 1446+point 2 split 4096 1447)/2)
    have hp : lowerPayment 1446 = (180192163361:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1446+point 2 split 4096 1447)/2 = (421786383:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421786383:ℝ)/168755200)/ClassicalSixthBranch.v ((421786383:ℝ)/168755200) = (702180947263:ℝ)/351135049656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1446
  · change lowerPayment 1447 ≤ lowerValue ((point 2 split 4096 1447+point 2 split 4096 1448)/2)
    have hp : lowerPayment 1447 = (180291655397:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1447+point 2 split 4096 1448)/2 = (84368929:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84368929:ℝ)/33751040)/ClassicalSixthBranch.v ((84368929:ℝ)/33751040) = (702103633589:ℝ)/351087041768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1447
  · change lowerPayment 1448 ≤ lowerValue ((point 2 split 4096 1448+point 2 split 4096 1449)/2)
    have hp : lowerPayment 1448 = (180391126726:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1448+point 2 split 4096 1449)/2 = (421902907:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421902907:ℝ)/168755200)/ClassicalSixthBranch.v ((421902907:ℝ)/168755200) = (140405263983:ℝ)/70207806776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1448
  · change lowerPayment 1449 ≤ lowerValue ((point 2 split 4096 1449+point 2 split 4096 1450)/2)
    have hp : lowerPayment 1449 = (180490577371:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1449+point 2 split 4096 1450)/2 = (421961169:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((421961169:ℝ)/168755200)/ClassicalSixthBranch.v ((421961169:ℝ)/168755200) = (701949006241:ℝ)/350991025992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1449
  · change lowerPayment 1450 ≤ lowerValue ((point 2 split 4096 1450+point 2 split 4096 1451)/2)
    have hp : lowerPayment 1450 = (180590007353:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1450+point 2 split 4096 1451)/2 = (422019431:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422019431:ℝ)/168755200)/ClassicalSixthBranch.v ((422019431:ℝ)/168755200) = (701871692567:ℝ)/350943018104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1450
  · change lowerPayment 1451 ≤ lowerValue ((point 2 split 4096 1451+point 2 split 4096 1452)/2)
    have hp : lowerPayment 1451 = (180689416694:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1451+point 2 split 4096 1452)/2 = (422077693:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422077693:ℝ)/168755200)/ClassicalSixthBranch.v ((422077693:ℝ)/168755200) = (701794378893:ℝ)/350895010216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1451
  · change lowerPayment 1452 ≤ lowerValue ((point 2 split 4096 1452+point 2 split 4096 1453)/2)
    have hp : lowerPayment 1452 = (180788805416:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1452+point 2 split 4096 1453)/2 = (84427191:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84427191:ℝ)/33751040)/ClassicalSixthBranch.v ((84427191:ℝ)/33751040) = (701717065219:ℝ)/350847002328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1452
  · change lowerPayment 1453 ≤ lowerValue ((point 2 split 4096 1453+point 2 split 4096 1454)/2)
    have hp : lowerPayment 1453 = (180888173541:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1453+point 2 split 4096 1454)/2 = (422194217:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422194217:ℝ)/168755200)/ClassicalSixthBranch.v ((422194217:ℝ)/168755200) = (140327950309:ℝ)/70159798888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1453
  · change lowerPayment 1454 ≤ lowerValue ((point 2 split 4096 1454+point 2 split 4096 1455)/2)
    have hp : lowerPayment 1454 = (180987521091:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1454+point 2 split 4096 1455)/2 = (422252479:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422252479:ℝ)/168755200)/ClassicalSixthBranch.v ((422252479:ℝ)/168755200) = (701562437871:ℝ)/350750986552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1454
  · change lowerPayment 1455 ≤ lowerValue ((point 2 split 4096 1455+point 2 split 4096 1456)/2)
    have hp : lowerPayment 1455 = (181086848088:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1455+point 2 split 4096 1456)/2 = (422310741:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((422310741:ℝ)/168755200)/ClassicalSixthBranch.v ((422310741:ℝ)/168755200) = (701485124197:ℝ)/350702978664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1455
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_090
