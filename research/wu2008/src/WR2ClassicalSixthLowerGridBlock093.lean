import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints093
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_093 (j : Fin 16) : lowerPayment (16*93+j.val) ≤
    lowerValue ((point 2 split 4096 (16*93+j.val)+point 2 split 4096 (16*93+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1488 ≤ lowerValue ((point 2 split 4096 1488+point 2 split 4096 1489)/2)
    have hp : lowerPayment 1488 = (184353251028:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1488+point 2 split 4096 1489)/2 = (424233387:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424233387:ℝ)/168755200)/ClassicalSixthBranch.v ((424233387:ℝ)/168755200) = (139786754591:ℝ)/69823743672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1488
  · change lowerPayment 1489 ≤ lowerValue ((point 2 split 4096 1489+point 2 split 4096 1490)/2)
    have hp : lowerPayment 1489 = (184451892139:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1489+point 2 split 4096 1490)/2 = (424291649:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424291649:ℝ)/168755200)/ClassicalSixthBranch.v ((424291649:ℝ)/168755200) = (698856459281:ℝ)/349070710472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1489
  · change lowerPayment 1490 ≤ lowerValue ((point 2 split 4096 1490+point 2 split 4096 1491)/2)
    have hp : lowerPayment 1490 = (184550513454:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1490+point 2 split 4096 1491)/2 = (424349911:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424349911:ℝ)/168755200)/ClassicalSixthBranch.v ((424349911:ℝ)/168755200) = (698779145607:ℝ)/349022702584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1490
  · change lowerPayment 1491 ≤ lowerValue ((point 2 split 4096 1491+point 2 split 4096 1492)/2)
    have hp : lowerPayment 1491 = (184649114995:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1491+point 2 split 4096 1492)/2 = (424408173:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424408173:ℝ)/168755200)/ClassicalSixthBranch.v ((424408173:ℝ)/168755200) = (698701831933:ℝ)/348974694696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1491
  · change lowerPayment 1492 ≤ lowerValue ((point 2 split 4096 1492+point 2 split 4096 1493)/2)
    have hp : lowerPayment 1492 = (184747696783:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1492+point 2 split 4096 1493)/2 = (84893287:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84893287:ℝ)/33751040)/ClassicalSixthBranch.v ((84893287:ℝ)/33751040) = (698624518259:ℝ)/348926686808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1492
  · change lowerPayment 1493 ≤ lowerValue ((point 2 split 4096 1493+point 2 split 4096 1494)/2)
    have hp : lowerPayment 1493 = (184846258840:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1493+point 2 split 4096 1494)/2 = (4121599:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4121599:ℝ)/1638400)/ClassicalSixthBranch.v ((4121599:ℝ)/1638400) = (1356402339:ℝ)/677434328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1493
  · change lowerPayment 1494 ≤ lowerValue ((point 2 split 4096 1494+point 2 split 4096 1495)/2)
    have hp : lowerPayment 1494 = (184944801187:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1494+point 2 split 4096 1495)/2 = (424582959:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424582959:ℝ)/168755200)/ClassicalSixthBranch.v ((424582959:ℝ)/168755200) = (698469890911:ℝ)/348830671032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1494
  · change lowerPayment 1495 ≤ lowerValue ((point 2 split 4096 1495+point 2 split 4096 1496)/2)
    have hp : lowerPayment 1495 = (185043323845:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1495+point 2 split 4096 1496)/2 = (424641221:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424641221:ℝ)/168755200)/ClassicalSixthBranch.v ((424641221:ℝ)/168755200) = (698392577237:ℝ)/348782663144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1495
  · change lowerPayment 1496 ≤ lowerValue ((point 2 split 4096 1496+point 2 split 4096 1497)/2)
    have hp : lowerPayment 1496 = (185141826836:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1496+point 2 split 4096 1497)/2 = (424699483:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424699483:ℝ)/168755200)/ClassicalSixthBranch.v ((424699483:ℝ)/168755200) = (698315263563:ℝ)/348734655256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1496
  · change lowerPayment 1497 ≤ lowerValue ((point 2 split 4096 1497+point 2 split 4096 1498)/2)
    have hp : lowerPayment 1497 = (185240310181:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1497+point 2 split 4096 1498)/2 = (84951549:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((84951549:ℝ)/33751040)/ClassicalSixthBranch.v ((84951549:ℝ)/33751040) = (698237949889:ℝ)/348686647368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1497
  · change lowerPayment 1498 ≤ lowerValue ((point 2 split 4096 1498+point 2 split 4096 1499)/2)
    have hp : lowerPayment 1498 = (185338773901:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1498+point 2 split 4096 1499)/2 = (424816007:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424816007:ℝ)/168755200)/ClassicalSixthBranch.v ((424816007:ℝ)/168755200) = (139632127243:ℝ)/69727727896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1498
  · change lowerPayment 1499 ≤ lowerValue ((point 2 split 4096 1499+point 2 split 4096 1500)/2)
    have hp : lowerPayment 1499 = (185437218018:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1499+point 2 split 4096 1500)/2 = (424874269:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424874269:ℝ)/168755200)/ClassicalSixthBranch.v ((424874269:ℝ)/168755200) = (698083322541:ℝ)/348590631592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1499
  · change lowerPayment 1500 ≤ lowerValue ((point 2 split 4096 1500+point 2 split 4096 1501)/2)
    have hp : lowerPayment 1500 = (185535642553:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1500+point 2 split 4096 1501)/2 = (424932531:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424932531:ℝ)/168755200)/ClassicalSixthBranch.v ((424932531:ℝ)/168755200) = (698006008867:ℝ)/348542623704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1500
  · change lowerPayment 1501 ≤ lowerValue ((point 2 split 4096 1501+point 2 split 4096 1502)/2)
    have hp : lowerPayment 1501 = (185634047528:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1501+point 2 split 4096 1502)/2 = (424990793:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((424990793:ℝ)/168755200)/ClassicalSixthBranch.v ((424990793:ℝ)/168755200) = (697928695193:ℝ)/348494615816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1501
  · change lowerPayment 1502 ≤ lowerValue ((point 2 split 4096 1502+point 2 split 4096 1503)/2)
    have hp : lowerPayment 1502 = (185732432963:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1502+point 2 split 4096 1503)/2 = (85009811:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85009811:ℝ)/33751040)/ClassicalSixthBranch.v ((85009811:ℝ)/33751040) = (697851381519:ℝ)/348446607928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1502
  · change lowerPayment 1503 ≤ lowerValue ((point 2 split 4096 1503+point 2 split 4096 1504)/2)
    have hp : lowerPayment 1503 = (185830798879:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1503+point 2 split 4096 1504)/2 = (425107317:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((425107317:ℝ)/168755200)/ClassicalSixthBranch.v ((425107317:ℝ)/168755200) = (139554813569:ℝ)/69679720008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1503
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_093
