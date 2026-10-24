import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints100
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_100 (j : Fin 16) : upperPayment (16*100+j.val) ≤
    upperValue ((point split endpoint 4096 (16*100+j.val)+point split endpoint 4096 (16*100+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1600 ≤ upperValue ((point split endpoint 4096 1600+point split endpoint 4096 1601)/2)
    have hp : upperPayment 1600 = (311346114670:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1600+point split endpoint 4096 1601)/2 = (616404127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616404127:ℝ)/168755200)*ClassicalSixthBranch.v ((616404127:ℝ)/168755200)/ClassicalSixthBranch.r = (123919552456017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1600
  · change upperPayment 1601 ≤ upperValue ((point split endpoint 4096 1601+point split endpoint 4096 1602)/2)
    have hp : upperPayment 1601 = (311257668585:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1601+point split endpoint 4096 1602)/2 = (616429277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616429277:ℝ)/168755200)*ClassicalSixthBranch.v ((616429277:ℝ)/168755200)/ClassicalSixthBranch.r = (123896775678425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1601
  · change upperPayment 1602 ≤ upperValue ((point split endpoint 4096 1602+point split endpoint 4096 1603)/2)
    have hp : upperPayment 1602 = (311169198186:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1602+point split endpoint 4096 1603)/2 = (616454427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616454427:ℝ)/168755200)*ClassicalSixthBranch.v ((616454427:ℝ)/168755200)/ClassicalSixthBranch.r = (123874000924905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1602
  · change upperPayment 1603 ≤ upperValue ((point split endpoint 4096 1603+point split endpoint 4096 1604)/2)
    have hp : upperPayment 1603 = (311080703469:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1603+point split endpoint 4096 1604)/2 = (616479577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616479577:ℝ)/168755200)*ClassicalSixthBranch.v ((616479577:ℝ)/168755200)/ClassicalSixthBranch.r = (123851228195457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1603
  · change upperPayment 1604 ≤ upperValue ((point split endpoint 4096 1604+point split endpoint 4096 1605)/2)
    have hp : upperPayment 1604 = (310992184428:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1604+point split endpoint 4096 1605)/2 = (616504727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616504727:ℝ)/168755200)*ClassicalSixthBranch.v ((616504727:ℝ)/168755200)/ClassicalSixthBranch.r = (123828457490081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1604
  · change upperPayment 1605 ≤ upperValue ((point split endpoint 4096 1605+point split endpoint 4096 1606)/2)
    have hp : upperPayment 1605 = (310903641059:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1605+point split endpoint 4096 1606)/2 = (616529877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616529877:ℝ)/168755200)*ClassicalSixthBranch.v ((616529877:ℝ)/168755200)/ClassicalSixthBranch.r = (123805688808777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1605
  · change upperPayment 1606 ≤ upperValue ((point split endpoint 4096 1606+point split endpoint 4096 1607)/2)
    have hp : upperPayment 1606 = (310815073359:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1606+point split endpoint 4096 1607)/2 = (616555027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616555027:ℝ)/168755200)*ClassicalSixthBranch.v ((616555027:ℝ)/168755200)/ClassicalSixthBranch.r = (123782922151545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1606
  · change upperPayment 1607 ≤ upperValue ((point split endpoint 4096 1607+point split endpoint 4096 1608)/2)
    have hp : upperPayment 1607 = (310726481322:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1607+point split endpoint 4096 1608)/2 = (616580177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616580177:ℝ)/168755200)*ClassicalSixthBranch.v ((616580177:ℝ)/168755200)/ClassicalSixthBranch.r = (123760157518385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1607
  · change upperPayment 1608 ≤ upperValue ((point split endpoint 4096 1608+point split endpoint 4096 1609)/2)
    have hp : upperPayment 1608 = (310637864945:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1608+point split endpoint 4096 1609)/2 = (616605327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616605327:ℝ)/168755200)*ClassicalSixthBranch.v ((616605327:ℝ)/168755200)/ClassicalSixthBranch.r = (123737394909297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1608
  · change upperPayment 1609 ≤ upperValue ((point split endpoint 4096 1609+point split endpoint 4096 1610)/2)
    have hp : upperPayment 1609 = (310549224222:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1609+point split endpoint 4096 1610)/2 = (616630477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616630477:ℝ)/168755200)*ClassicalSixthBranch.v ((616630477:ℝ)/168755200)/ClassicalSixthBranch.r = (123714634324281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1609
  · change upperPayment 1610 ≤ upperValue ((point split endpoint 4096 1610+point split endpoint 4096 1611)/2)
    have hp : upperPayment 1610 = (310460559150:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1610+point split endpoint 4096 1611)/2 = (616655627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616655627:ℝ)/168755200)*ClassicalSixthBranch.v ((616655627:ℝ)/168755200)/ClassicalSixthBranch.r = (123691875763337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1610
  · change upperPayment 1611 ≤ upperValue ((point split endpoint 4096 1611+point split endpoint 4096 1612)/2)
    have hp : upperPayment 1611 = (310371869724:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1611+point split endpoint 4096 1612)/2 = (616680777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616680777:ℝ)/168755200)*ClassicalSixthBranch.v ((616680777:ℝ)/168755200)/ClassicalSixthBranch.r = (123669119226465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1611
  · change upperPayment 1612 ≤ upperValue ((point split endpoint 4096 1612+point split endpoint 4096 1613)/2)
    have hp : upperPayment 1612 = (310283155939:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1612+point split endpoint 4096 1613)/2 = (616705927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616705927:ℝ)/168755200)*ClassicalSixthBranch.v ((616705927:ℝ)/168755200)/ClassicalSixthBranch.r = (123646364713665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1612
  · change upperPayment 1613 ≤ upperValue ((point split endpoint 4096 1613+point split endpoint 4096 1614)/2)
    have hp : upperPayment 1613 = (310194417792:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1613+point split endpoint 4096 1614)/2 = (616731077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616731077:ℝ)/168755200)*ClassicalSixthBranch.v ((616731077:ℝ)/168755200)/ClassicalSixthBranch.r = (123623612224937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1613
  · change upperPayment 1614 ≤ upperValue ((point split endpoint 4096 1614+point split endpoint 4096 1615)/2)
    have hp : upperPayment 1614 = (310105655277:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1614+point split endpoint 4096 1615)/2 = (616756227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616756227:ℝ)/168755200)*ClassicalSixthBranch.v ((616756227:ℝ)/168755200)/ClassicalSixthBranch.r = (123600861760281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1614
  · change upperPayment 1615 ≤ upperValue ((point split endpoint 4096 1615+point split endpoint 4096 1616)/2)
    have hp : upperPayment 1615 = (310016868391:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1615+point split endpoint 4096 1616)/2 = (616781377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((616781377:ℝ)/168755200)*ClassicalSixthBranch.v ((616781377:ℝ)/168755200)/ClassicalSixthBranch.r = (123578113319697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1615
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_100
