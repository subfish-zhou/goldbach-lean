import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints009
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_009 (j : Fin 16) : lowerPayment (16*9+j.val) ≤
    lowerValue ((point 2 split 4096 (16*9+j.val)+point 2 split 4096 (16*9+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 144 ≤ lowerValue ((point 2 split 4096 144+point 2 split 4096 145)/2)
    have hp : lowerPayment 144 = (22790881653:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 144+point 2 split 4096 145)/2 = (345929259:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345929259:ℝ)/168755200)/ClassicalSixthBranch.v ((345929259:ℝ)/168755200) = (802843350811:ℝ)/413641319832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_144
  · change lowerPayment 145 ≤ lowerValue ((point 2 split 4096 145+point 2 split 4096 146)/2)
    have hp : lowerPayment 145 = (22943348540:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 145+point 2 split 4096 146)/2 = (345987521:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345987521:ℝ)/168755200)/ClassicalSixthBranch.v ((345987521:ℝ)/168755200) = (802766037137:ℝ)/413593311944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_145
  · change lowerPayment 146 ≤ lowerValue ((point 2 split 4096 146+point 2 split 4096 147)/2)
    have hp : lowerPayment 146 = (23095746361:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 146+point 2 split 4096 147)/2 = (346045783:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((346045783:ℝ)/168755200)/ClassicalSixthBranch.v ((346045783:ℝ)/168755200) = (802688723463:ℝ)/413545304056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_146
  · change lowerPayment 147 ≤ lowerValue ((point 2 split 4096 147+point 2 split 4096 148)/2)
    have hp : lowerPayment 147 = (23248075178:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 147+point 2 split 4096 148)/2 = (69220809:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69220809:ℝ)/33751040)/ClassicalSixthBranch.v ((69220809:ℝ)/33751040) = (802611409789:ℝ)/413497296168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_147
  · change lowerPayment 148 ≤ lowerValue ((point 2 split 4096 148+point 2 split 4096 149)/2)
    have hp : lowerPayment 148 = (23400335054:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 148+point 2 split 4096 149)/2 = (346162307:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((346162307:ℝ)/168755200)/ClassicalSixthBranch.v ((346162307:ℝ)/168755200) = (160506819223:ℝ)/82689857656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_148
  · change lowerPayment 149 ≤ lowerValue ((point 2 split 4096 149+point 2 split 4096 150)/2)
    have hp : lowerPayment 149 = (23552526050:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 149+point 2 split 4096 150)/2 = (346220569:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((346220569:ℝ)/168755200)/ClassicalSixthBranch.v ((346220569:ℝ)/168755200) = (802456782441:ℝ)/413401280392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_149
  · change lowerPayment 150 ≤ lowerValue ((point 2 split 4096 150+point 2 split 4096 151)/2)
    have hp : lowerPayment 150 = (23704648229:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 150+point 2 split 4096 151)/2 = (346278831:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((346278831:ℝ)/168755200)/ClassicalSixthBranch.v ((346278831:ℝ)/168755200) = (802379468767:ℝ)/413353272504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_150
  · change lowerPayment 151 ≤ lowerValue ((point 2 split 4096 151+point 2 split 4096 152)/2)
    have hp : lowerPayment 151 = (23856701654:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 151+point 2 split 4096 152)/2 = (346337093:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((346337093:ℝ)/168755200)/ClassicalSixthBranch.v ((346337093:ℝ)/168755200) = (802302155093:ℝ)/413305264616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_151
  · change lowerPayment 152 ≤ lowerValue ((point 2 split 4096 152+point 2 split 4096 153)/2)
    have hp : lowerPayment 152 = (24008686386:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 152+point 2 split 4096 153)/2 = (69279071:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69279071:ℝ)/33751040)/ClassicalSixthBranch.v ((69279071:ℝ)/33751040) = (802224841419:ℝ)/413257256728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_152
  · change lowerPayment 153 ≤ lowerValue ((point 2 split 4096 153+point 2 split 4096 154)/2)
    have hp : lowerPayment 153 = (24160602488:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 153+point 2 split 4096 154)/2 = (346453617:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((346453617:ℝ)/168755200)/ClassicalSixthBranch.v ((346453617:ℝ)/168755200) = (160429505549:ℝ)/82641849768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_153
  · change lowerPayment 154 ≤ lowerValue ((point 2 split 4096 154+point 2 split 4096 155)/2)
    have hp : lowerPayment 154 = (24312450023:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 154+point 2 split 4096 155)/2 = (3364193:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((3364193:ℝ)/1638400)/ClassicalSixthBranch.v ((3364193:ℝ)/1638400) = (7787089457:ℝ)/4011274184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_154
  · change lowerPayment 155 ≤ lowerValue ((point 2 split 4096 155+point 2 split 4096 156)/2)
    have hp : lowerPayment 155 = (24464229051:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 155+point 2 split 4096 156)/2 = (346570141:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((346570141:ℝ)/168755200)/ClassicalSixthBranch.v ((346570141:ℝ)/168755200) = (801992900397:ℝ)/413113233064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_155
  · change lowerPayment 156 ≤ lowerValue ((point 2 split 4096 156+point 2 split 4096 157)/2)
    have hp : lowerPayment 156 = (24615939636:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 156+point 2 split 4096 157)/2 = (346628403:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((346628403:ℝ)/168755200)/ClassicalSixthBranch.v ((346628403:ℝ)/168755200) = (801915586723:ℝ)/413065225176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_156
  · change lowerPayment 157 ≤ lowerValue ((point 2 split 4096 157+point 2 split 4096 158)/2)
    have hp : lowerPayment 157 = (24767581838:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 157+point 2 split 4096 158)/2 = (69337333:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69337333:ℝ)/33751040)/ClassicalSixthBranch.v ((69337333:ℝ)/33751040) = (801838273049:ℝ)/413017217288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_157
  · change lowerPayment 158 ≤ lowerValue ((point 2 split 4096 158+point 2 split 4096 159)/2)
    have hp : lowerPayment 158 = (24919155720:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 158+point 2 split 4096 159)/2 = (346744927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((346744927:ℝ)/168755200)/ClassicalSixthBranch.v ((346744927:ℝ)/168755200) = (32070438375:ℝ)/16518768376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_158
  · change lowerPayment 159 ≤ lowerValue ((point 2 split 4096 159+point 2 split 4096 160)/2)
    have hp : lowerPayment 159 = (25070661344:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 159+point 2 split 4096 160)/2 = (346803189:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((346803189:ℝ)/168755200)/ClassicalSixthBranch.v ((346803189:ℝ)/168755200) = (801683645701:ℝ)/412921201512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_159
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_009
