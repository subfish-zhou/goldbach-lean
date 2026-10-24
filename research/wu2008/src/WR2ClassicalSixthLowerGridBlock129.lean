import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints129
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_129 (j : Fin 16) : lowerPayment (16*129+j.val) ≤
    lowerValue ((point 2 split 4096 (16*129+j.val)+point 2 split 4096 (16*129+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2064 ≤ lowerValue ((point 2 split 4096 2064+point 2 split 4096 2065)/2)
    have hp : lowerPayment 2064 = (238521632623:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2064+point 2 split 4096 2065)/2 = (457792299:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457792299:ℝ)/168755200)/ClassicalSixthBranch.v ((457792299:ℝ)/168755200) = (654401096731:ℝ)/321466174872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2064
  · change lowerPayment 2065 ≤ lowerValue ((point 2 split 4096 2065+point 2 split 4096 2066)/2)
    have hp : lowerPayment 2065 = (238612084815:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2065+point 2 split 4096 2066)/2 = (457850561:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457850561:ℝ)/168755200)/ClassicalSixthBranch.v ((457850561:ℝ)/168755200) = (654323783057:ℝ)/321418166984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2065
  · change lowerPayment 2066 ≤ lowerValue ((point 2 split 4096 2066+point 2 split 4096 2067)/2)
    have hp : lowerPayment 2066 = (238702527899:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2066+point 2 split 4096 2067)/2 = (457908823:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((457908823:ℝ)/168755200)/ClassicalSixthBranch.v ((457908823:ℝ)/168755200) = (654246469383:ℝ)/321370159096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2066
  · change lowerPayment 2067 ≤ lowerValue ((point 2 split 4096 2067+point 2 split 4096 2068)/2)
    have hp : lowerPayment 2067 = (238792961893:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2067+point 2 split 4096 2068)/2 = (91593417:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91593417:ℝ)/33751040)/ClassicalSixthBranch.v ((91593417:ℝ)/33751040) = (654169155709:ℝ)/321322151208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2067
  · change lowerPayment 2068 ≤ lowerValue ((point 2 split 4096 2068+point 2 split 4096 2069)/2)
    have hp : lowerPayment 2068 = (238883386812:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2068+point 2 split 4096 2069)/2 = (458025347:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458025347:ℝ)/168755200)/ClassicalSixthBranch.v ((458025347:ℝ)/168755200) = (130818368407:ℝ)/64254828664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2068
  · change lowerPayment 2069 ≤ lowerValue ((point 2 split 4096 2069+point 2 split 4096 2070)/2)
    have hp : lowerPayment 2069 = (238973802672:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2069+point 2 split 4096 2070)/2 = (458083609:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458083609:ℝ)/168755200)/ClassicalSixthBranch.v ((458083609:ℝ)/168755200) = (654014528361:ℝ)/321226135432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2069
  · change lowerPayment 2070 ≤ lowerValue ((point 2 split 4096 2070+point 2 split 4096 2071)/2)
    have hp : lowerPayment 2070 = (239064209490:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2070+point 2 split 4096 2071)/2 = (458141871:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458141871:ℝ)/168755200)/ClassicalSixthBranch.v ((458141871:ℝ)/168755200) = (653937214687:ℝ)/321178127544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2070
  · change lowerPayment 2071 ≤ lowerValue ((point 2 split 4096 2071+point 2 split 4096 2072)/2)
    have hp : lowerPayment 2071 = (239154607283:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2071+point 2 split 4096 2072)/2 = (458200133:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458200133:ℝ)/168755200)/ClassicalSixthBranch.v ((458200133:ℝ)/168755200) = (653859901013:ℝ)/321130119656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2071
  · change lowerPayment 2072 ≤ lowerValue ((point 2 split 4096 2072+point 2 split 4096 2073)/2)
    have hp : lowerPayment 2072 = (239244996066:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2072+point 2 split 4096 2073)/2 = (91651679:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91651679:ℝ)/33751040)/ClassicalSixthBranch.v ((91651679:ℝ)/33751040) = (653782587339:ℝ)/321082111768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2072
  · change lowerPayment 2073 ≤ lowerValue ((point 2 split 4096 2073+point 2 split 4096 2074)/2)
    have hp : lowerPayment 2073 = (239335375855:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2073+point 2 split 4096 2074)/2 = (458316657:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458316657:ℝ)/168755200)/ClassicalSixthBranch.v ((458316657:ℝ)/168755200) = (130741054733:ℝ)/64206820776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2073
  · change lowerPayment 2074 ≤ lowerValue ((point 2 split 4096 2074+point 2 split 4096 2075)/2)
    have hp : lowerPayment 2074 = (239425746668:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2074+point 2 split 4096 2075)/2 = (458374919:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458374919:ℝ)/168755200)/ClassicalSixthBranch.v ((458374919:ℝ)/168755200) = (653627959991:ℝ)/320986095992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2074
  · change lowerPayment 2075 ≤ lowerValue ((point 2 split 4096 2075+point 2 split 4096 2076)/2)
    have hp : lowerPayment 2075 = (239516108519:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2075+point 2 split 4096 2076)/2 = (458433181:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458433181:ℝ)/168755200)/ClassicalSixthBranch.v ((458433181:ℝ)/168755200) = (653550646317:ℝ)/320938088104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2075
  · change lowerPayment 2076 ≤ lowerValue ((point 2 split 4096 2076+point 2 split 4096 2077)/2)
    have hp : lowerPayment 2076 = (239606461427:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2076+point 2 split 4096 2077)/2 = (458491443:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458491443:ℝ)/168755200)/ClassicalSixthBranch.v ((458491443:ℝ)/168755200) = (653473332643:ℝ)/320890080216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2076
  · change lowerPayment 2077 ≤ lowerValue ((point 2 split 4096 2077+point 2 split 4096 2078)/2)
    have hp : lowerPayment 2077 = (239696805406:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2077+point 2 split 4096 2078)/2 = (91709941:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91709941:ℝ)/33751040)/ClassicalSixthBranch.v ((91709941:ℝ)/33751040) = (653396018969:ℝ)/320842072328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2077
  · change lowerPayment 2078 ≤ lowerValue ((point 2 split 4096 2078+point 2 split 4096 2079)/2)
    have hp : lowerPayment 2078 = (239787140473:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2078+point 2 split 4096 2079)/2 = (458607967:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458607967:ℝ)/168755200)/ClassicalSixthBranch.v ((458607967:ℝ)/168755200) = (130663741059:ℝ)/64158812888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2078
  · change lowerPayment 2079 ≤ lowerValue ((point 2 split 4096 2079+point 2 split 4096 2080)/2)
    have hp : lowerPayment 2079 = (239877466644:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2079+point 2 split 4096 2080)/2 = (458666229:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458666229:ℝ)/168755200)/ClassicalSixthBranch.v ((458666229:ℝ)/168755200) = (653241391621:ℝ)/320746056552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2079
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_129
