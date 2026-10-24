import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints132
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_132 (j : Fin 16) : lowerPayment (16*132+j.val) ≤
    lowerValue ((point 2 split 4096 (16*132+j.val)+point 2 split 4096 (16*132+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2112 ≤ lowerValue ((point 2 split 4096 2112+point 2 split 4096 2113)/2)
    have hp : lowerPayment 2112 = (242853345725:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2112+point 2 split 4096 2113)/2 = (18423555:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18423555:ℝ)/6750208)/ClassicalSixthBranch.v ((18423555:ℝ)/6750208) = (650690040379:ℝ)/319161796248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2112
  · change lowerPayment 2113 ≤ lowerValue ((point 2 split 4096 2113+point 2 split 4096 2114)/2)
    have hp : lowerPayment 2113 = (242943379062:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2113+point 2 split 4096 2114)/2 = (460647137:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460647137:ℝ)/168755200)/ClassicalSixthBranch.v ((460647137:ℝ)/168755200) = (130122545341:ℝ)/63822757672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2113
  · change lowerPayment 2114 ≤ lowerValue ((point 2 split 4096 2114+point 2 split 4096 2115)/2)
    have hp : lowerPayment 2114 = (243033404069:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2114+point 2 split 4096 2115)/2 = (460705399:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460705399:ℝ)/168755200)/ClassicalSixthBranch.v ((460705399:ℝ)/168755200) = (650535413031:ℝ)/319065780472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2114
  · change lowerPayment 2115 ≤ lowerValue ((point 2 split 4096 2115+point 2 split 4096 2116)/2)
    have hp : lowerPayment 2115 = (243123420761:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2115+point 2 split 4096 2116)/2 = (460763661:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460763661:ℝ)/168755200)/ClassicalSixthBranch.v ((460763661:ℝ)/168755200) = (650458099357:ℝ)/319017772584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2115
  · change lowerPayment 2116 ≤ lowerValue ((point 2 split 4096 2116+point 2 split 4096 2117)/2)
    have hp : lowerPayment 2116 = (243213429154:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2116+point 2 split 4096 2117)/2 = (460821923:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460821923:ℝ)/168755200)/ClassicalSixthBranch.v ((460821923:ℝ)/168755200) = (650380785683:ℝ)/318969764696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2116
  · change lowerPayment 2117 ≤ lowerValue ((point 2 split 4096 2117+point 2 split 4096 2118)/2)
    have hp : lowerPayment 2117 = (243303429264:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2117+point 2 split 4096 2118)/2 = (92176037:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92176037:ℝ)/33751040)/ClassicalSixthBranch.v ((92176037:ℝ)/33751040) = (650303472009:ℝ)/318921756808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2117
  · change lowerPayment 2118 ≤ lowerValue ((point 2 split 4096 2118+point 2 split 4096 2119)/2)
    have hp : lowerPayment 2118 = (243393421107:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2118+point 2 split 4096 2119)/2 = (460938447:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460938447:ℝ)/168755200)/ClassicalSixthBranch.v ((460938447:ℝ)/168755200) = (130045231667:ℝ)/63774749784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2118
  · change lowerPayment 2119 ≤ lowerValue ((point 2 split 4096 2119+point 2 split 4096 2120)/2)
    have hp : lowerPayment 2119 = (243483404700:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2119+point 2 split 4096 2120)/2 = (460996709:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((460996709:ℝ)/168755200)/ClassicalSixthBranch.v ((460996709:ℝ)/168755200) = (650148844661:ℝ)/318825741032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2119
  · change lowerPayment 2120 ≤ lowerValue ((point 2 split 4096 2120+point 2 split 4096 2121)/2)
    have hp : lowerPayment 2120 = (243573380057:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2120+point 2 split 4096 2121)/2 = (461054971:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461054971:ℝ)/168755200)/ClassicalSixthBranch.v ((461054971:ℝ)/168755200) = (650071530987:ℝ)/318777733144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2120
  · change lowerPayment 2121 ≤ lowerValue ((point 2 split 4096 2121+point 2 split 4096 2122)/2)
    have hp : lowerPayment 2121 = (243663347196:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2121+point 2 split 4096 2122)/2 = (461113233:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461113233:ℝ)/168755200)/ClassicalSixthBranch.v ((461113233:ℝ)/168755200) = (649994217313:ℝ)/318729725256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2121
  · change lowerPayment 2122 ≤ lowerValue ((point 2 split 4096 2122+point 2 split 4096 2123)/2)
    have hp : lowerPayment 2122 = (243753306133:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2122+point 2 split 4096 2123)/2 = (92234299:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92234299:ℝ)/33751040)/ClassicalSixthBranch.v ((92234299:ℝ)/33751040) = (649916903639:ℝ)/318681717368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2122
  · change lowerPayment 2123 ≤ lowerValue ((point 2 split 4096 2123+point 2 split 4096 2124)/2)
    have hp : lowerPayment 2123 = (243843256882:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2123+point 2 split 4096 2124)/2 = (461229757:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461229757:ℝ)/168755200)/ClassicalSixthBranch.v ((461229757:ℝ)/168755200) = (129967917993:ℝ)/63726741896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2123
  · change lowerPayment 2124 ≤ lowerValue ((point 2 split 4096 2124+point 2 split 4096 2125)/2)
    have hp : lowerPayment 2124 = (243933199461:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2124+point 2 split 4096 2125)/2 = (461288019:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461288019:ℝ)/168755200)/ClassicalSixthBranch.v ((461288019:ℝ)/168755200) = (649762276291:ℝ)/318585701592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2124
  · change lowerPayment 2125 ≤ lowerValue ((point 2 split 4096 2125+point 2 split 4096 2126)/2)
    have hp : lowerPayment 2125 = (244023133885:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2125+point 2 split 4096 2126)/2 = (461346281:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461346281:ℝ)/168755200)/ClassicalSixthBranch.v ((461346281:ℝ)/168755200) = (649684962617:ℝ)/318537693704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2125
  · change lowerPayment 2126 ≤ lowerValue ((point 2 split 4096 2126+point 2 split 4096 2127)/2)
    have hp : lowerPayment 2126 = (244113060170:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2126+point 2 split 4096 2127)/2 = (461404543:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((461404543:ℝ)/168755200)/ClassicalSixthBranch.v ((461404543:ℝ)/168755200) = (649607648943:ℝ)/318489685816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2126
  · change lowerPayment 2127 ≤ lowerValue ((point 2 split 4096 2127+point 2 split 4096 2128)/2)
    have hp : lowerPayment 2127 = (244202978332:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2127+point 2 split 4096 2128)/2 = (92292561:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92292561:ℝ)/33751040)/ClassicalSixthBranch.v ((92292561:ℝ)/33751040) = (649530335269:ℝ)/318441677928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2127
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_132
