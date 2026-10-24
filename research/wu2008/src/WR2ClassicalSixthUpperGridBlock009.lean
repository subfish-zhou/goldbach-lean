import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints009
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_009 (j : Fin 16) : upperPayment (16*9+j.val) ≤
    upperValue ((point split endpoint 4096 (16*9+j.val)+point split endpoint 4096 (16*9+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 144 ≤ upperValue ((point split endpoint 4096 144+point split endpoint 4096 145)/2)
    have hp : upperPayment 144 = (416291179023:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 144+point split endpoint 4096 145)/2 = (579785727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579785727:ℝ)/168755200)*ClassicalSixthBranch.v ((579785727:ℝ)/168755200)/ClassicalSixthBranch.r = (159229465704081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_144
  · change upperPayment 145 ≤ upperValue ((point split endpoint 4096 145+point split endpoint 4096 146)/2)
    have hp : upperPayment 145 = (416234300918:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 145+point split endpoint 4096 146)/2 = (579810877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579810877:ℝ)/168755200)*ClassicalSixthBranch.v ((579810877:ℝ)/168755200)/ClassicalSixthBranch.r = (159203741877657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_145
  · change upperPayment 146 ≤ upperValue ((point split endpoint 4096 146+point split endpoint 4096 147)/2)
    have hp : upperPayment 146 = (416177403248:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 146+point split endpoint 4096 147)/2 = (579836027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579836027:ℝ)/168755200)*ClassicalSixthBranch.v ((579836027:ℝ)/168755200)/ClassicalSixthBranch.r = (159178020075305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_146
  · change upperPayment 147 ≤ upperValue ((point split endpoint 4096 147+point split endpoint 4096 148)/2)
    have hp : upperPayment 147 = (416120486013:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 147+point split endpoint 4096 148)/2 = (579861177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579861177:ℝ)/168755200)*ClassicalSixthBranch.v ((579861177:ℝ)/168755200)/ClassicalSixthBranch.r = (159152300297025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_147
  · change upperPayment 148 ≤ upperValue ((point split endpoint 4096 148+point split endpoint 4096 149)/2)
    have hp : upperPayment 148 = (416063549208:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 148+point split endpoint 4096 149)/2 = (579886327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579886327:ℝ)/168755200)*ClassicalSixthBranch.v ((579886327:ℝ)/168755200)/ClassicalSixthBranch.r = (159126582542817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_148
  · change upperPayment 149 ≤ upperValue ((point split endpoint 4096 149+point split endpoint 4096 150)/2)
    have hp : upperPayment 149 = (416006592832:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 149+point split endpoint 4096 150)/2 = (579911477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579911477:ℝ)/168755200)*ClassicalSixthBranch.v ((579911477:ℝ)/168755200)/ClassicalSixthBranch.r = (159100866812681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_149
  · change upperPayment 150 ≤ upperValue ((point split endpoint 4096 150+point split endpoint 4096 151)/2)
    have hp : upperPayment 150 = (415949616883:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 150+point split endpoint 4096 151)/2 = (579936627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579936627:ℝ)/168755200)*ClassicalSixthBranch.v ((579936627:ℝ)/168755200)/ClassicalSixthBranch.r = (159075153106617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_150
  · change upperPayment 151 ≤ upperValue ((point split endpoint 4096 151+point split endpoint 4096 152)/2)
    have hp : upperPayment 151 = (415892621358:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 151+point split endpoint 4096 152)/2 = (579961777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579961777:ℝ)/168755200)*ClassicalSixthBranch.v ((579961777:ℝ)/168755200)/ClassicalSixthBranch.r = (159049441424625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_151
  · change upperPayment 152 ≤ upperValue ((point split endpoint 4096 152+point split endpoint 4096 153)/2)
    have hp : upperPayment 152 = (415835606256:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 152+point split endpoint 4096 153)/2 = (579986927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579986927:ℝ)/168755200)*ClassicalSixthBranch.v ((579986927:ℝ)/168755200)/ClassicalSixthBranch.r = (159023731766705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_152
  · change upperPayment 153 ≤ upperValue ((point split endpoint 4096 153+point split endpoint 4096 154)/2)
    have hp : upperPayment 153 = (415778571573:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 153+point split endpoint 4096 154)/2 = (580012077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580012077:ℝ)/168755200)*ClassicalSixthBranch.v ((580012077:ℝ)/168755200)/ClassicalSixthBranch.r = (158998024132857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_153
  · change upperPayment 154 ≤ upperValue ((point split endpoint 4096 154+point split endpoint 4096 155)/2)
    have hp : upperPayment 154 = (415721517307:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 154+point split endpoint 4096 155)/2 = (580037227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580037227:ℝ)/168755200)*ClassicalSixthBranch.v ((580037227:ℝ)/168755200)/ClassicalSixthBranch.r = (158972318523081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_154
  · change upperPayment 155 ≤ upperValue ((point split endpoint 4096 155+point split endpoint 4096 156)/2)
    have hp : upperPayment 155 = (415664443457:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 155+point split endpoint 4096 156)/2 = (580062377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580062377:ℝ)/168755200)*ClassicalSixthBranch.v ((580062377:ℝ)/168755200)/ClassicalSixthBranch.r = (158946614937377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_155
  · change upperPayment 156 ≤ upperValue ((point split endpoint 4096 156+point split endpoint 4096 157)/2)
    have hp : upperPayment 156 = (415607350020:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 156+point split endpoint 4096 157)/2 = (580087527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580087527:ℝ)/168755200)*ClassicalSixthBranch.v ((580087527:ℝ)/168755200)/ClassicalSixthBranch.r = (158920913375745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_156
  · change upperPayment 157 ≤ upperValue ((point split endpoint 4096 157+point split endpoint 4096 158)/2)
    have hp : upperPayment 157 = (415550236993:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 157+point split endpoint 4096 158)/2 = (580112677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580112677:ℝ)/168755200)*ClassicalSixthBranch.v ((580112677:ℝ)/168755200)/ClassicalSixthBranch.r = (158895213838185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_157
  · change upperPayment 158 ≤ upperValue ((point split endpoint 4096 158+point split endpoint 4096 159)/2)
    have hp : upperPayment 158 = (415493104375:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 158+point split endpoint 4096 159)/2 = (580137827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580137827:ℝ)/168755200)*ClassicalSixthBranch.v ((580137827:ℝ)/168755200)/ClassicalSixthBranch.r = (158869516324697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_158
  · change upperPayment 159 ≤ upperValue ((point split endpoint 4096 159+point split endpoint 4096 160)/2)
    have hp : upperPayment 159 = (415435952162:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 159+point split endpoint 4096 160)/2 = (580162977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((580162977:ℝ)/168755200)*ClassicalSixthBranch.v ((580162977:ℝ)/168755200)/ClassicalSixthBranch.r = (158843820835281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_159
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_009
