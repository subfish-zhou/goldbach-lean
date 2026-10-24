import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints130
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_130 (j : Fin 16) : lowerPayment (16*130+j.val) ≤
    lowerValue ((point 2 split 4096 (16*130+j.val)+point 2 split 4096 (16*130+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2080 ≤ lowerValue ((point 2 split 4096 2080+point 2 split 4096 2081)/2)
    have hp : lowerPayment 2080 = (239967783936:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2080+point 2 split 4096 2081)/2 = (458724491:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458724491:ℝ)/168755200)/ClassicalSixthBranch.v ((458724491:ℝ)/168755200) = (653164077947:ℝ)/320698048664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2080
  · change lowerPayment 2081 ≤ lowerValue ((point 2 split 4096 2081+point 2 split 4096 2082)/2)
    have hp : lowerPayment 2081 = (240058092364:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2081+point 2 split 4096 2082)/2 = (458782753:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458782753:ℝ)/168755200)/ClassicalSixthBranch.v ((458782753:ℝ)/168755200) = (653086764273:ℝ)/320650040776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2081
  · change lowerPayment 2082 ≤ lowerValue ((point 2 split 4096 2082+point 2 split 4096 2083)/2)
    have hp : lowerPayment 2082 = (240148391945:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2082+point 2 split 4096 2083)/2 = (91768203:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91768203:ℝ)/33751040)/ClassicalSixthBranch.v ((91768203:ℝ)/33751040) = (653009450599:ℝ)/320602032888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2082
  · change lowerPayment 2083 ≤ lowerValue ((point 2 split 4096 2083+point 2 split 4096 2084)/2)
    have hp : lowerPayment 2083 = (240238682696:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2083+point 2 split 4096 2084)/2 = (458899277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458899277:ℝ)/168755200)/ClassicalSixthBranch.v ((458899277:ℝ)/168755200) = (26117285477:ℝ)/12822161000 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2083
  · change lowerPayment 2084 ≤ lowerValue ((point 2 split 4096 2084+point 2 split 4096 2085)/2)
    have hp : lowerPayment 2084 = (240328964631:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2084+point 2 split 4096 2085)/2 = (458957539:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((458957539:ℝ)/168755200)/ClassicalSixthBranch.v ((458957539:ℝ)/168755200) = (652854823251:ℝ)/320506017112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2084
  · change lowerPayment 2085 ≤ lowerValue ((point 2 split 4096 2085+point 2 split 4096 2086)/2)
    have hp : lowerPayment 2085 = (240419237769:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2085+point 2 split 4096 2086)/2 = (459015801:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459015801:ℝ)/168755200)/ClassicalSixthBranch.v ((459015801:ℝ)/168755200) = (652777509577:ℝ)/320458009224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2085
  · change lowerPayment 2086 ≤ lowerValue ((point 2 split 4096 2086+point 2 split 4096 2087)/2)
    have hp : lowerPayment 2086 = (240509502124:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2086+point 2 split 4096 2087)/2 = (459074063:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459074063:ℝ)/168755200)/ClassicalSixthBranch.v ((459074063:ℝ)/168755200) = (652700195903:ℝ)/320410001336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2086
  · change lowerPayment 2087 ≤ lowerValue ((point 2 split 4096 2087+point 2 split 4096 2088)/2)
    have hp : lowerPayment 2087 = (240599757713:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2087+point 2 split 4096 2088)/2 = (18365293:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18365293:ℝ)/6750208)/ClassicalSixthBranch.v ((18365293:ℝ)/6750208) = (652622882229:ℝ)/320361993448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2087
  · change lowerPayment 2088 ≤ lowerValue ((point 2 split 4096 2088+point 2 split 4096 2089)/2)
    have hp : lowerPayment 2088 = (240690004552:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2088+point 2 split 4096 2089)/2 = (459190587:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459190587:ℝ)/168755200)/ClassicalSixthBranch.v ((459190587:ℝ)/168755200) = (130509113711:ℝ)/64062797112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2088
  · change lowerPayment 2089 ≤ lowerValue ((point 2 split 4096 2089+point 2 split 4096 2090)/2)
    have hp : lowerPayment 2089 = (240780242657:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2089+point 2 split 4096 2090)/2 = (459248849:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459248849:ℝ)/168755200)/ClassicalSixthBranch.v ((459248849:ℝ)/168755200) = (652468254881:ℝ)/320265977672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2089
  · change lowerPayment 2090 ≤ lowerValue ((point 2 split 4096 2090+point 2 split 4096 2091)/2)
    have hp : lowerPayment 2090 = (240870472045:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2090+point 2 split 4096 2091)/2 = (459307111:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459307111:ℝ)/168755200)/ClassicalSixthBranch.v ((459307111:ℝ)/168755200) = (652390941207:ℝ)/320217969784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2090
  · change lowerPayment 2091 ≤ lowerValue ((point 2 split 4096 2091+point 2 split 4096 2092)/2)
    have hp : lowerPayment 2091 = (240960692732:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2091+point 2 split 4096 2092)/2 = (459365373:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459365373:ℝ)/168755200)/ClassicalSixthBranch.v ((459365373:ℝ)/168755200) = (652313627533:ℝ)/320169961896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2091
  · change lowerPayment 2092 ≤ lowerValue ((point 2 split 4096 2092+point 2 split 4096 2093)/2)
    have hp : lowerPayment 2092 = (241050904733:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2092+point 2 split 4096 2093)/2 = (91884727:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91884727:ℝ)/33751040)/ClassicalSixthBranch.v ((91884727:ℝ)/33751040) = (652236313859:ℝ)/320121954008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2092
  · change lowerPayment 2093 ≤ lowerValue ((point 2 split 4096 2093+point 2 split 4096 2094)/2)
    have hp : lowerPayment 2093 = (241141108066:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2093+point 2 split 4096 2094)/2 = (459481897:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459481897:ℝ)/168755200)/ClassicalSixthBranch.v ((459481897:ℝ)/168755200) = (130431800037:ℝ)/64014789224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2093
  · change lowerPayment 2094 ≤ lowerValue ((point 2 split 4096 2094+point 2 split 4096 2095)/2)
    have hp : lowerPayment 2094 = (241231302746:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2094+point 2 split 4096 2095)/2 = (459540159:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459540159:ℝ)/168755200)/ClassicalSixthBranch.v ((459540159:ℝ)/168755200) = (652081686511:ℝ)/320025938232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2094
  · change lowerPayment 2095 ≤ lowerValue ((point 2 split 4096 2095+point 2 split 4096 2096)/2)
    have hp : lowerPayment 2095 = (241321488788:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2095+point 2 split 4096 2096)/2 = (459598421:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459598421:ℝ)/168755200)/ClassicalSixthBranch.v ((459598421:ℝ)/168755200) = (652004372837:ℝ)/319977930344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2095
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_130
