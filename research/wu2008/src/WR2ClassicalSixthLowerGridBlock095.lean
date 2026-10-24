import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints095
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_095 (j : Fin 16) : lowerPayment (16*95+j.val) ≤
    lowerValue ((point 2 split 4096 (16*95+j.val)+point 2 split 4096 (16*95+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1520 ≤ lowerValue ((point 2 split 4096 1520+point 2 split 4096 1521)/2)
    have hp : lowerPayment 1520 = (187500053742:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1520+point 2 split 4096 1521)/2 = (426097771:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426097771:ℝ)/168755200)/ClassicalSixthBranch.v ((426097771:ℝ)/168755200) = (696459735387:ℝ)/347582465944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1520
  · change lowerPayment 1521 ≤ lowerValue ((point 2 split 4096 1521+point 2 split 4096 1522)/2)
    have hp : lowerPayment 1521 = (187598071956:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1521+point 2 split 4096 1522)/2 = (426156033:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426156033:ℝ)/168755200)/ClassicalSixthBranch.v ((426156033:ℝ)/168755200) = (696382421713:ℝ)/347534458056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1521
  · change lowerPayment 1522 ≤ lowerValue ((point 2 split 4096 1522+point 2 split 4096 1523)/2)
    have hp : lowerPayment 1522 = (187696071053:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1522+point 2 split 4096 1523)/2 = (85242859:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85242859:ℝ)/33751040)/ClassicalSixthBranch.v ((85242859:ℝ)/33751040) = (696305108039:ℝ)/347486450168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1522
  · change lowerPayment 1523 ≤ lowerValue ((point 2 split 4096 1523+point 2 split 4096 1524)/2)
    have hp : lowerPayment 1523 = (187794051055:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1523+point 2 split 4096 1524)/2 = (426272557:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426272557:ℝ)/168755200)/ClassicalSixthBranch.v ((426272557:ℝ)/168755200) = (139245558873:ℝ)/69487688456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1523
  · change lowerPayment 1524 ≤ lowerValue ((point 2 split 4096 1524+point 2 split 4096 1525)/2)
    have hp : lowerPayment 1524 = (187892011983:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1524+point 2 split 4096 1525)/2 = (426330819:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426330819:ℝ)/168755200)/ClassicalSixthBranch.v ((426330819:ℝ)/168755200) = (696150480691:ℝ)/347390434392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1524
  · change lowerPayment 1525 ≤ lowerValue ((point 2 split 4096 1525+point 2 split 4096 1526)/2)
    have hp : lowerPayment 1525 = (187989953858:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1525+point 2 split 4096 1526)/2 = (426389081:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426389081:ℝ)/168755200)/ClassicalSixthBranch.v ((426389081:ℝ)/168755200) = (696073167017:ℝ)/347342426504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1525
  · change lowerPayment 1526 ≤ lowerValue ((point 2 split 4096 1526+point 2 split 4096 1527)/2)
    have hp : lowerPayment 1526 = (188087876700:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1526+point 2 split 4096 1527)/2 = (426447343:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426447343:ℝ)/168755200)/ClassicalSixthBranch.v ((426447343:ℝ)/168755200) = (695995853343:ℝ)/347294418616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1526
  · change lowerPayment 1527 ≤ lowerValue ((point 2 split 4096 1527+point 2 split 4096 1528)/2)
    have hp : lowerPayment 1527 = (188185780531:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1527+point 2 split 4096 1528)/2 = (85301121:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85301121:ℝ)/33751040)/ClassicalSixthBranch.v ((85301121:ℝ)/33751040) = (695918539669:ℝ)/347246410728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1527
  · change lowerPayment 1528 ≤ lowerValue ((point 2 split 4096 1528+point 2 split 4096 1529)/2)
    have hp : lowerPayment 1528 = (188283665372:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1528+point 2 split 4096 1529)/2 = (426563867:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426563867:ℝ)/168755200)/ClassicalSixthBranch.v ((426563867:ℝ)/168755200) = (139168245199:ℝ)/69439680568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1528
  · change lowerPayment 1529 ≤ lowerValue ((point 2 split 4096 1529+point 2 split 4096 1530)/2)
    have hp : lowerPayment 1529 = (188381531244:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1529+point 2 split 4096 1530)/2 = (426622129:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426622129:ℝ)/168755200)/ClassicalSixthBranch.v ((426622129:ℝ)/168755200) = (695763912321:ℝ)/347150394952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1529
  · change lowerPayment 1530 ≤ lowerValue ((point 2 split 4096 1530+point 2 split 4096 1531)/2)
    have hp : lowerPayment 1530 = (188479378167:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1530+point 2 split 4096 1531)/2 = (426680391:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426680391:ℝ)/168755200)/ClassicalSixthBranch.v ((426680391:ℝ)/168755200) = (695686598647:ℝ)/347102387064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1530
  · change lowerPayment 1531 ≤ lowerValue ((point 2 split 4096 1531+point 2 split 4096 1532)/2)
    have hp : lowerPayment 1531 = (188577206163:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1531+point 2 split 4096 1532)/2 = (426738653:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426738653:ℝ)/168755200)/ClassicalSixthBranch.v ((426738653:ℝ)/168755200) = (695609284973:ℝ)/347054379176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1531
  · change lowerPayment 1532 ≤ lowerValue ((point 2 split 4096 1532+point 2 split 4096 1533)/2)
    have hp : lowerPayment 1532 = (188675015252:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1532+point 2 split 4096 1533)/2 = (85359383:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((85359383:ℝ)/33751040)/ClassicalSixthBranch.v ((85359383:ℝ)/33751040) = (695531971299:ℝ)/347006371288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1532
  · change lowerPayment 1533 ≤ lowerValue ((point 2 split 4096 1533+point 2 split 4096 1534)/2)
    have hp : lowerPayment 1533 = (188772805455:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1533+point 2 split 4096 1534)/2 = (426855177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426855177:ℝ)/168755200)/ClassicalSixthBranch.v ((426855177:ℝ)/168755200) = (27818186305:ℝ)/13878334536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1533
  · change lowerPayment 1534 ≤ lowerValue ((point 2 split 4096 1534+point 2 split 4096 1535)/2)
    have hp : lowerPayment 1534 = (188870576794:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1534+point 2 split 4096 1535)/2 = (426913439:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426913439:ℝ)/168755200)/ClassicalSixthBranch.v ((426913439:ℝ)/168755200) = (695377343951:ℝ)/346910355512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1534
  · change lowerPayment 1535 ≤ lowerValue ((point 2 split 4096 1535+point 2 split 4096 1536)/2)
    have hp : lowerPayment 1535 = (188968329289:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1535+point 2 split 4096 1536)/2 = (426971701:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((426971701:ℝ)/168755200)/ClassicalSixthBranch.v ((426971701:ℝ)/168755200) = (695300030277:ℝ)/346862347624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1535
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_095
