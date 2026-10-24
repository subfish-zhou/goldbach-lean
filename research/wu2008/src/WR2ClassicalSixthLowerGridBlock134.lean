import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints134
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_134 (j : Fin 16) : lowerPayment (16*134+j.val) ≤
    lowerValue ((point 2 split 4096 (16*134+j.val)+point 2 split 4096 (16*134+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2144 ≤ lowerValue ((point 2 split 4096 2144+point 2 split 4096 2145)/2)
    have hp : lowerPayment 2144 = (245730359753:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2144+point 2 split 4096 2145)/2 = (462453259:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462453259:ℝ)/168755200)/ClassicalSixthBranch.v ((462453259:ℝ)/168755200) = (648216002811:ℝ)/317625543832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2144
  · change lowerPayment 2145 ≤ lowerValue ((point 2 split 4096 2145+point 2 split 4096 2146)/2)
    have hp : lowerPayment 2145 = (245820134430:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2145+point 2 split 4096 2146)/2 = (462511521:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462511521:ℝ)/168755200)/ClassicalSixthBranch.v ((462511521:ℝ)/168755200) = (648138689137:ℝ)/317577535944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2145
  · change lowerPayment 2146 ≤ lowerValue ((point 2 split 4096 2146+point 2 split 4096 2147)/2)
    have hp : lowerPayment 2146 = (245909901287:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2146+point 2 split 4096 2147)/2 = (462569783:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462569783:ℝ)/168755200)/ClassicalSixthBranch.v ((462569783:ℝ)/168755200) = (648061375463:ℝ)/317529528056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2146
  · change lowerPayment 2147 ≤ lowerValue ((point 2 split 4096 2147+point 2 split 4096 2148)/2)
    have hp : lowerPayment 2147 = (245999660339:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2147+point 2 split 4096 2148)/2 = (92525609:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92525609:ℝ)/33751040)/ClassicalSixthBranch.v ((92525609:ℝ)/33751040) = (647984061789:ℝ)/317481520168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2147
  · change lowerPayment 2148 ≤ lowerValue ((point 2 split 4096 2148+point 2 split 4096 2149)/2)
    have hp : lowerPayment 2148 = (246089411603:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2148+point 2 split 4096 2149)/2 = (462686307:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462686307:ℝ)/168755200)/ClassicalSixthBranch.v ((462686307:ℝ)/168755200) = (129581349623:ℝ)/63486702456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2148
  · change lowerPayment 2149 ≤ lowerValue ((point 2 split 4096 2149+point 2 split 4096 2150)/2)
    have hp : lowerPayment 2149 = (246179155094:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2149+point 2 split 4096 2150)/2 = (462744569:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462744569:ℝ)/168755200)/ClassicalSixthBranch.v ((462744569:ℝ)/168755200) = (647829434441:ℝ)/317385504392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2149
  · change lowerPayment 2150 ≤ lowerValue ((point 2 split 4096 2150+point 2 split 4096 2151)/2)
    have hp : lowerPayment 2150 = (246268890828:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2150+point 2 split 4096 2151)/2 = (462802831:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462802831:ℝ)/168755200)/ClassicalSixthBranch.v ((462802831:ℝ)/168755200) = (647752120767:ℝ)/317337496504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2150
  · change lowerPayment 2151 ≤ lowerValue ((point 2 split 4096 2151+point 2 split 4096 2152)/2)
    have hp : lowerPayment 2151 = (246358618821:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2151+point 2 split 4096 2152)/2 = (462861093:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462861093:ℝ)/168755200)/ClassicalSixthBranch.v ((462861093:ℝ)/168755200) = (647674807093:ℝ)/317289488616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2151
  · change lowerPayment 2152 ≤ lowerValue ((point 2 split 4096 2152+point 2 split 4096 2153)/2)
    have hp : lowerPayment 2152 = (246448339089:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2152+point 2 split 4096 2153)/2 = (92583871:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92583871:ℝ)/33751040)/ClassicalSixthBranch.v ((92583871:ℝ)/33751040) = (647597493419:ℝ)/317241480728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2152
  · change lowerPayment 2153 ≤ lowerValue ((point 2 split 4096 2153+point 2 split 4096 2154)/2)
    have hp : lowerPayment 2153 = (246538051647:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2153+point 2 split 4096 2154)/2 = (462977617:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((462977617:ℝ)/168755200)/ClassicalSixthBranch.v ((462977617:ℝ)/168755200) = (129504035949:ℝ)/63438694568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2153
  · change lowerPayment 2154 ≤ lowerValue ((point 2 split 4096 2154+point 2 split 4096 2155)/2)
    have hp : lowerPayment 2154 = (246627756512:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2154+point 2 split 4096 2155)/2 = (463035879:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463035879:ℝ)/168755200)/ClassicalSixthBranch.v ((463035879:ℝ)/168755200) = (647442866071:ℝ)/317145464952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2154
  · change lowerPayment 2155 ≤ lowerValue ((point 2 split 4096 2155+point 2 split 4096 2156)/2)
    have hp : lowerPayment 2155 = (246717453700:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2155+point 2 split 4096 2156)/2 = (463094141:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463094141:ℝ)/168755200)/ClassicalSixthBranch.v ((463094141:ℝ)/168755200) = (647365552397:ℝ)/317097457064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2155
  · change lowerPayment 2156 ≤ lowerValue ((point 2 split 4096 2156+point 2 split 4096 2157)/2)
    have hp : lowerPayment 2156 = (246807143225:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2156+point 2 split 4096 2157)/2 = (463152403:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463152403:ℝ)/168755200)/ClassicalSixthBranch.v ((463152403:ℝ)/168755200) = (647288238723:ℝ)/317049449176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2156
  · change lowerPayment 2157 ≤ lowerValue ((point 2 split 4096 2157+point 2 split 4096 2158)/2)
    have hp : lowerPayment 2157 = (246896825105:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2157+point 2 split 4096 2158)/2 = (92642133:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((92642133:ℝ)/33751040)/ClassicalSixthBranch.v ((92642133:ℝ)/33751040) = (647210925049:ℝ)/317001441288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2157
  · change lowerPayment 2158 ≤ lowerValue ((point 2 split 4096 2158+point 2 split 4096 2159)/2)
    have hp : lowerPayment 2158 = (246986499354:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2158+point 2 split 4096 2159)/2 = (463268927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463268927:ℝ)/168755200)/ClassicalSixthBranch.v ((463268927:ℝ)/168755200) = (25885344455:ℝ)/12678137336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2158
  · change lowerPayment 2159 ≤ lowerValue ((point 2 split 4096 2159+point 2 split 4096 2160)/2)
    have hp : lowerPayment 2159 = (247076165989:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2159+point 2 split 4096 2160)/2 = (463327189:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((463327189:ℝ)/168755200)/ClassicalSixthBranch.v ((463327189:ℝ)/168755200) = (647056297701:ℝ)/316905425512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2159
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_134
