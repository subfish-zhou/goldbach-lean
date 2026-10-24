import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints100
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_100 (j : Fin 16) : lowerPayment (16*100+j.val) ≤
    lowerValue ((point 2 split 4096 (16*100+j.val)+point 2 split 4096 (16*100+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1600 ≤ lowerValue ((point 2 split 4096 1600+point 2 split 4096 1601)/2)
    have hp : lowerPayment 1600 = (195282812523:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1600+point 2 split 4096 1601)/2 = (430758731:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430758731:ℝ)/168755200)/ClassicalSixthBranch.v ((430758731:ℝ)/168755200) = (690274641467:ℝ)/343741834904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1600
  · change lowerPayment 1601 ≤ lowerValue ((point 2 split 4096 1601+point 2 split 4096 1602)/2)
    have hp : lowerPayment 1601 = (195379366925:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1601+point 2 split 4096 1602)/2 = (430816993:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430816993:ℝ)/168755200)/ClassicalSixthBranch.v ((430816993:ℝ)/168755200) = (690197327793:ℝ)/343693827016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1601
  · change lowerPayment 1602 ≤ lowerValue ((point 2 split 4096 1602+point 2 split 4096 1603)/2)
    have hp : lowerPayment 1602 = (195475903856:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1602+point 2 split 4096 1603)/2 = (86175051:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86175051:ℝ)/33751040)/ClassicalSixthBranch.v ((86175051:ℝ)/33751040) = (690120014119:ℝ)/343645819128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1602
  · change lowerPayment 1603 ≤ lowerValue ((point 2 split 4096 1603+point 2 split 4096 1604)/2)
    have hp : lowerPayment 1603 = (195572423336:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1603+point 2 split 4096 1604)/2 = (430933517:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430933517:ℝ)/168755200)/ClassicalSixthBranch.v ((430933517:ℝ)/168755200) = (138008540089:ℝ)/68719562248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1603
  · change lowerPayment 1604 ≤ lowerValue ((point 2 split 4096 1604+point 2 split 4096 1605)/2)
    have hp : lowerPayment 1604 = (195668925387:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1604+point 2 split 4096 1605)/2 = (430991779:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((430991779:ℝ)/168755200)/ClassicalSixthBranch.v ((430991779:ℝ)/168755200) = (689965386771:ℝ)/343549803352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1604
  · change lowerPayment 1605 ≤ lowerValue ((point 2 split 4096 1605+point 2 split 4096 1606)/2)
    have hp : lowerPayment 1605 = (195765410027:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1605+point 2 split 4096 1606)/2 = (431050041:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431050041:ℝ)/168755200)/ClassicalSixthBranch.v ((431050041:ℝ)/168755200) = (689888073097:ℝ)/343501795464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1605
  · change lowerPayment 1606 ≤ lowerValue ((point 2 split 4096 1606+point 2 split 4096 1607)/2)
    have hp : lowerPayment 1606 = (195861877276:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1606+point 2 split 4096 1607)/2 = (431108303:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431108303:ℝ)/168755200)/ClassicalSixthBranch.v ((431108303:ℝ)/168755200) = (689810759423:ℝ)/343453787576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1606
  · change lowerPayment 1607 ≤ lowerValue ((point 2 split 4096 1607+point 2 split 4096 1608)/2)
    have hp : lowerPayment 1607 = (195958327156:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1607+point 2 split 4096 1608)/2 = (86233313:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((86233313:ℝ)/33751040)/ClassicalSixthBranch.v ((86233313:ℝ)/33751040) = (689733445749:ℝ)/343405779688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1607
  · change lowerPayment 1608 ≤ lowerValue ((point 2 split 4096 1608+point 2 split 4096 1609)/2)
    have hp : lowerPayment 1608 = (196054759685:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1608+point 2 split 4096 1609)/2 = (431224827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431224827:ℝ)/168755200)/ClassicalSixthBranch.v ((431224827:ℝ)/168755200) = (27586245283:ℝ)/13734310872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1608
  · change lowerPayment 1609 ≤ lowerValue ((point 2 split 4096 1609+point 2 split 4096 1610)/2)
    have hp : lowerPayment 1609 = (196151174885:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1609+point 2 split 4096 1610)/2 = (431283089:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431283089:ℝ)/168755200)/ClassicalSixthBranch.v ((431283089:ℝ)/168755200) = (689578818401:ℝ)/343309763912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1609
  · change lowerPayment 1610 ≤ lowerValue ((point 2 split 4096 1610+point 2 split 4096 1611)/2)
    have hp : lowerPayment 1610 = (196247572774:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1610+point 2 split 4096 1611)/2 = (431341351:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431341351:ℝ)/168755200)/ClassicalSixthBranch.v ((431341351:ℝ)/168755200) = (689501504727:ℝ)/343261756024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1610
  · change lowerPayment 1611 ≤ lowerValue ((point 2 split 4096 1611+point 2 split 4096 1612)/2)
    have hp : lowerPayment 1611 = (196343953374:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1611+point 2 split 4096 1612)/2 = (431399613:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431399613:ℝ)/168755200)/ClassicalSixthBranch.v ((431399613:ℝ)/168755200) = (689424191053:ℝ)/343213748136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1611
  · change lowerPayment 1612 ≤ lowerValue ((point 2 split 4096 1612+point 2 split 4096 1613)/2)
    have hp : lowerPayment 1612 = (196440316703:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1612+point 2 split 4096 1613)/2 = (17258315:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17258315:ℝ)/6750208)/ClassicalSixthBranch.v ((17258315:ℝ)/6750208) = (689346877379:ℝ)/343165740248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1612
  · change lowerPayment 1613 ≤ lowerValue ((point 2 split 4096 1613+point 2 split 4096 1614)/2)
    have hp : lowerPayment 1613 = (196536662783:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1613+point 2 split 4096 1614)/2 = (431516137:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431516137:ℝ)/168755200)/ClassicalSixthBranch.v ((431516137:ℝ)/168755200) = (137853912741:ℝ)/68623546472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1613
  · change lowerPayment 1614 ≤ lowerValue ((point 2 split 4096 1614+point 2 split 4096 1615)/2)
    have hp : lowerPayment 1614 = (196632991632:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1614+point 2 split 4096 1615)/2 = (431574399:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431574399:ℝ)/168755200)/ClassicalSixthBranch.v ((431574399:ℝ)/168755200) = (689192250031:ℝ)/343069724472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1614
  · change lowerPayment 1615 ≤ lowerValue ((point 2 split 4096 1615+point 2 split 4096 1616)/2)
    have hp : lowerPayment 1615 = (196729303272:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1615+point 2 split 4096 1616)/2 = (431632661:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((431632661:ℝ)/168755200)/ClassicalSixthBranch.v ((431632661:ℝ)/168755200) = (689114936357:ℝ)/343021716584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1615
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_100
