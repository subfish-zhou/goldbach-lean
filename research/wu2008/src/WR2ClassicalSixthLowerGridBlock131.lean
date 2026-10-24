import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints131
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_131 (j : Fin 16) : lowerPayment (16*131+j.val) ≤
    lowerValue ((point 2 split 4096 (16*131+j.val)+point 2 split 4096 (16*131+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2096 ≤ lowerValue ((point 2 split 4096 2096+point 2 split 4096 2097)/2)
    have hp : lowerPayment 2096 = (241411666211:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2096+point 2 split 4096 2097)/2 = (459656683:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459656683:ℝ)/168755200)/ClassicalSixthBranch.v ((459656683:ℝ)/168755200) = (651927059163:ℝ)/319929922456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2096
  · change lowerPayment 2097 ≤ lowerValue ((point 2 split 4096 2097+point 2 split 4096 2098)/2)
    have hp : lowerPayment 2097 = (241501835029:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2097+point 2 split 4096 2098)/2 = (91942989:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((91942989:ℝ)/33751040)/ClassicalSixthBranch.v ((91942989:ℝ)/33751040) = (651849745489:ℝ)/319881914568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2097
  · change lowerPayment 2098 ≤ lowerValue ((point 2 split 4096 2098+point 2 split 4096 2099)/2)
    have hp : lowerPayment 2098 = (241591995258:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2098+point 2 split 4096 2099)/2 = (459773207:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459773207:ℝ)/168755200)/ClassicalSixthBranch.v ((459773207:ℝ)/168755200) = (130354486363:ℝ)/63966781336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2098
  · change lowerPayment 2099 ≤ lowerValue ((point 2 split 4096 2099+point 2 split 4096 2100)/2)
    have hp : lowerPayment 2099 = (241682146916:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2099+point 2 split 4096 2100)/2 = (459831469:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459831469:ℝ)/168755200)/ClassicalSixthBranch.v ((459831469:ℝ)/168755200) = (651695118141:ℝ)/319785898792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2099
  · change lowerPayment 2100 ≤ lowerValue ((point 2 split 4096 2100+point 2 split 4096 2101)/2)
    have hp : lowerPayment 2100 = (241772290017:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2100+point 2 split 4096 2101)/2 = (459889731:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459889731:ℝ)/168755200)/ClassicalSixthBranch.v ((459889731:ℝ)/168755200) = (651617804467:ℝ)/319737890904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2100
  · change lowerPayment 2101 ≤ lowerValue ((point 2 split 4096 2101+point 2 split 4096 2102)/2)
    have hp : lowerPayment 2101 = (241862424579:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2101+point 2 split 4096 2102)/2 = (459947993:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((459947993:ℝ)/168755200)/ClassicalSixthBranch.v ((459947993:ℝ)/168755200) = (651540490793:ℝ)/319689883016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2101
  · change lowerPayment 2102 ≤ lowerValue ((point 2 split 4096 2102+point 2 split 4096 2103)/2)
    have hp : lowerPayment 2102 = (241952550617:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2102+point 2 split 4096 2103)/2 = (92001251:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92001251:ℝ)/33751040)/ClassicalSixthBranch.v ((92001251:ℝ)/33751040) = (651463177119:ℝ)/319641875128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2102
  · change lowerPayment 2103 ≤ lowerValue ((point 2 split 4096 2103+point 2 split 4096 2104)/2)
    have hp : lowerPayment 2103 = (242042668147:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2103+point 2 split 4096 2104)/2 = (460064517:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460064517:ℝ)/168755200)/ClassicalSixthBranch.v ((460064517:ℝ)/168755200) = (130277172689:ℝ)/63918773448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2103
  · change lowerPayment 2104 ≤ lowerValue ((point 2 split 4096 2104+point 2 split 4096 2105)/2)
    have hp : lowerPayment 2104 = (242132777185:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2104+point 2 split 4096 2105)/2 = (460122779:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460122779:ℝ)/168755200)/ClassicalSixthBranch.v ((460122779:ℝ)/168755200) = (651308549771:ℝ)/319545859352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2104
  · change lowerPayment 2105 ≤ lowerValue ((point 2 split 4096 2105+point 2 split 4096 2106)/2)
    have hp : lowerPayment 2105 = (242222877748:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2105+point 2 split 4096 2106)/2 = (460181041:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460181041:ℝ)/168755200)/ClassicalSixthBranch.v ((460181041:ℝ)/168755200) = (490754511:ℝ)/240767032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2105
  · change lowerPayment 2106 ≤ lowerValue ((point 2 split 4096 2106+point 2 split 4096 2107)/2)
    have hp : lowerPayment 2106 = (242312969852:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2106+point 2 split 4096 2107)/2 = (460239303:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460239303:ℝ)/168755200)/ClassicalSixthBranch.v ((460239303:ℝ)/168755200) = (651153922423:ℝ)/319449843576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2106
  · change lowerPayment 2107 ≤ lowerValue ((point 2 split 4096 2107+point 2 split 4096 2108)/2)
    have hp : lowerPayment 2107 = (242403053512:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2107+point 2 split 4096 2108)/2 = (92059513:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92059513:ℝ)/33751040)/ClassicalSixthBranch.v ((92059513:ℝ)/33751040) = (651076608749:ℝ)/319401835688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2107
  · change lowerPayment 2108 ≤ lowerValue ((point 2 split 4096 2108+point 2 split 4096 2109)/2)
    have hp : lowerPayment 2108 = (242493128745:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2108+point 2 split 4096 2109)/2 = (460355827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460355827:ℝ)/168755200)/ClassicalSixthBranch.v ((460355827:ℝ)/168755200) = (26039971803:ℝ)/12774153112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2108
  · change lowerPayment 2109 ≤ lowerValue ((point 2 split 4096 2109+point 2 split 4096 2110)/2)
    have hp : lowerPayment 2109 = (242583195566:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2109+point 2 split 4096 2110)/2 = (460414089:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460414089:ℝ)/168755200)/ClassicalSixthBranch.v ((460414089:ℝ)/168755200) = (650921981401:ℝ)/319305819912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2109
  · change lowerPayment 2110 ≤ lowerValue ((point 2 split 4096 2110+point 2 split 4096 2111)/2)
    have hp : lowerPayment 2110 = (242673253993:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2110+point 2 split 4096 2111)/2 = (460472351:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460472351:ℝ)/168755200)/ClassicalSixthBranch.v ((460472351:ℝ)/168755200) = (650844667727:ℝ)/319257812024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2110
  · change lowerPayment 2111 ≤ lowerValue ((point 2 split 4096 2111+point 2 split 4096 2112)/2)
    have hp : lowerPayment 2111 = (242763304040:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2111+point 2 split 4096 2112)/2 = (4471171:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4471171:ℝ)/1638400)/ClassicalSixthBranch.v ((4471171:ℝ)/1638400) = (6318129651:ℝ)/3099124312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2111
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_131
