import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints074
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_074 (j : Fin 16) : lowerPayment (16*74+j.val) ≤
    lowerValue ((point 2 split 4096 (16*74+j.val)+point 2 split 4096 (16*74+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1184 ≤ lowerValue ((point 2 split 4096 1184+point 2 split 4096 1185)/2)
    have hp : lowerPayment 1184 = (153342483722:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1184+point 2 split 4096 1185)/2 = (3946813:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((3946813:ℝ)/1638400)/ClassicalSixthBranch.v ((3946813:ℝ)/1638400) = (7013952717:ℝ)/3531195304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1184
  · change lowerPayment 1185 ≤ lowerValue ((point 2 split 4096 1185+point 2 split 4096 1186)/2)
    have hp : lowerPayment 1185 = (153448200176:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1185+point 2 split 4096 1186)/2 = (406580001:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((406580001:ℝ)/168755200)/ClassicalSixthBranch.v ((406580001:ℝ)/168755200) = (722359816177:ℝ)/363665108424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1185
  · change lowerPayment 1186 ≤ lowerValue ((point 2 split 4096 1186+point 2 split 4096 1187)/2)
    have hp : lowerPayment 1186 = (153553889670:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1186+point 2 split 4096 1187)/2 = (406638263:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((406638263:ℝ)/168755200)/ClassicalSixthBranch.v ((406638263:ℝ)/168755200) = (722282502503:ℝ)/363617100536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1186
  · change lowerPayment 1187 ≤ lowerValue ((point 2 split 4096 1187+point 2 split 4096 1188)/2)
    have hp : lowerPayment 1187 = (153659552232:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1187+point 2 split 4096 1188)/2 = (16267861:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16267861:ℝ)/6750208)/ClassicalSixthBranch.v ((16267861:ℝ)/6750208) = (722205188829:ℝ)/363569092648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1187
  · change lowerPayment 1188 ≤ lowerValue ((point 2 split 4096 1188+point 2 split 4096 1189)/2)
    have hp : lowerPayment 1188 = (153765187887:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1188+point 2 split 4096 1189)/2 = (406754787:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((406754787:ℝ)/168755200)/ClassicalSixthBranch.v ((406754787:ℝ)/168755200) = (144425575031:ℝ)/72704216952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1188
  · change lowerPayment 1189 ≤ lowerValue ((point 2 split 4096 1189+point 2 split 4096 1190)/2)
    have hp : lowerPayment 1189 = (153870796661:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1189+point 2 split 4096 1190)/2 = (406813049:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((406813049:ℝ)/168755200)/ClassicalSixthBranch.v ((406813049:ℝ)/168755200) = (722050561481:ℝ)/363473076872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1189
  · change lowerPayment 1190 ≤ lowerValue ((point 2 split 4096 1190+point 2 split 4096 1191)/2)
    have hp : lowerPayment 1190 = (153976378580:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1190+point 2 split 4096 1191)/2 = (406871311:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((406871311:ℝ)/168755200)/ClassicalSixthBranch.v ((406871311:ℝ)/168755200) = (721973247807:ℝ)/363425068984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1190
  · change lowerPayment 1191 ≤ lowerValue ((point 2 split 4096 1191+point 2 split 4096 1192)/2)
    have hp : lowerPayment 1191 = (154081933670:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1191+point 2 split 4096 1192)/2 = (406929573:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((406929573:ℝ)/168755200)/ClassicalSixthBranch.v ((406929573:ℝ)/168755200) = (721895934133:ℝ)/363377061096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1191
  · change lowerPayment 1192 ≤ lowerValue ((point 2 split 4096 1192+point 2 split 4096 1193)/2)
    have hp : lowerPayment 1192 = (154187461956:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1192+point 2 split 4096 1193)/2 = (81397567:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81397567:ℝ)/33751040)/ClassicalSixthBranch.v ((81397567:ℝ)/33751040) = (721818620459:ℝ)/363329053208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1192
  · change lowerPayment 1193 ≤ lowerValue ((point 2 split 4096 1193+point 2 split 4096 1194)/2)
    have hp : lowerPayment 1193 = (154292963465:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1193+point 2 split 4096 1194)/2 = (407046097:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407046097:ℝ)/168755200)/ClassicalSixthBranch.v ((407046097:ℝ)/168755200) = (144348261357:ℝ)/72656209064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1193
  · change lowerPayment 1194 ≤ lowerValue ((point 2 split 4096 1194+point 2 split 4096 1195)/2)
    have hp : lowerPayment 1194 = (154398438223:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1194+point 2 split 4096 1195)/2 = (407104359:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407104359:ℝ)/168755200)/ClassicalSixthBranch.v ((407104359:ℝ)/168755200) = (721663993111:ℝ)/363233037432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1194
  · change lowerPayment 1195 ≤ lowerValue ((point 2 split 4096 1195+point 2 split 4096 1196)/2)
    have hp : lowerPayment 1195 = (154503886254:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1195+point 2 split 4096 1196)/2 = (407162621:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407162621:ℝ)/168755200)/ClassicalSixthBranch.v ((407162621:ℝ)/168755200) = (721586679437:ℝ)/363185029544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1195
  · change lowerPayment 1196 ≤ lowerValue ((point 2 split 4096 1196+point 2 split 4096 1197)/2)
    have hp : lowerPayment 1196 = (154609307586:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1196+point 2 split 4096 1197)/2 = (407220883:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407220883:ℝ)/168755200)/ClassicalSixthBranch.v ((407220883:ℝ)/168755200) = (721509365763:ℝ)/363137021656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1196
  · change lowerPayment 1197 ≤ lowerValue ((point 2 split 4096 1197+point 2 split 4096 1198)/2)
    have hp : lowerPayment 1197 = (154714702243:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1197+point 2 split 4096 1198)/2 = (81455829:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81455829:ℝ)/33751040)/ClassicalSixthBranch.v ((81455829:ℝ)/33751040) = (721432052089:ℝ)/363089013768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1197
  · change lowerPayment 1198 ≤ lowerValue ((point 2 split 4096 1198+point 2 split 4096 1199)/2)
    have hp : lowerPayment 1198 = (154820070252:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1198+point 2 split 4096 1199)/2 = (407337407:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407337407:ℝ)/168755200)/ClassicalSixthBranch.v ((407337407:ℝ)/168755200) = (144270947683:ℝ)/72608201176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1198
  · change lowerPayment 1199 ≤ lowerValue ((point 2 split 4096 1199+point 2 split 4096 1200)/2)
    have hp : lowerPayment 1199 = (154925411639:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1199+point 2 split 4096 1200)/2 = (407395669:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((407395669:ℝ)/168755200)/ClassicalSixthBranch.v ((407395669:ℝ)/168755200) = (721277424741:ℝ)/362992997992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1199
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_074
