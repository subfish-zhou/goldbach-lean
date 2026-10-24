import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints074
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_074 (j : Fin 16) : upperPayment (16*74+j.val) ≤
    upperValue ((point split endpoint 4096 (16*74+j.val)+point split endpoint 4096 (16*74+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1184 ≤ upperValue ((point split endpoint 4096 1184+point split endpoint 4096 1185)/2)
    have hp : upperPayment 1184 = (346081705487:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1184+point split endpoint 4096 1185)/2 = (605941727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605941727:ℝ)/168755200)*ClassicalSixthBranch.v ((605941727:ℝ)/168755200)/ClassicalSixthBranch.r = (133570251843281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1184
  · change upperPayment 1185 ≤ upperValue ((point split endpoint 4096 1185+point split endpoint 4096 1186)/2)
    have hp : upperPayment 1185 = (346003013653:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1185+point split endpoint 4096 1186)/2 = (605966877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605966877:ℝ)/168755200)*ClassicalSixthBranch.v ((605966877:ℝ)/168755200)/ClassicalSixthBranch.r = (133546633051737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1185
  · change upperPayment 1186 ≤ upperValue ((point split endpoint 4096 1186+point split endpoint 4096 1187)/2)
    have hp : upperPayment 1186 = (345924299185:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1186+point split endpoint 4096 1187)/2 = (605992027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605992027:ℝ)/168755200)*ClassicalSixthBranch.v ((605992027:ℝ)/168755200)/ClassicalSixthBranch.r = (133523016284265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1186
  · change upperPayment 1187 ≤ upperValue ((point split endpoint 4096 1187+point split endpoint 4096 1188)/2)
    have hp : upperPayment 1187 = (345845562080:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1187+point split endpoint 4096 1188)/2 = (606017177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606017177:ℝ)/168755200)*ClassicalSixthBranch.v ((606017177:ℝ)/168755200)/ClassicalSixthBranch.r = (133499401540865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1187
  · change upperPayment 1188 ≤ upperValue ((point split endpoint 4096 1188+point split endpoint 4096 1189)/2)
    have hp : upperPayment 1188 = (345766802334:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1188+point split endpoint 4096 1189)/2 = (606042327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606042327:ℝ)/168755200)*ClassicalSixthBranch.v ((606042327:ℝ)/168755200)/ClassicalSixthBranch.r = (133475788821537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1188
  · change upperPayment 1189 ≤ upperValue ((point split endpoint 4096 1189+point split endpoint 4096 1190)/2)
    have hp : upperPayment 1189 = (345688019942:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1189+point split endpoint 4096 1190)/2 = (606067477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606067477:ℝ)/168755200)*ClassicalSixthBranch.v ((606067477:ℝ)/168755200)/ClassicalSixthBranch.r = (133452178126281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1189
  · change upperPayment 1190 ≤ upperValue ((point split endpoint 4096 1190+point split endpoint 4096 1191)/2)
    have hp : upperPayment 1190 = (345609214902:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1190+point split endpoint 4096 1191)/2 = (606092627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606092627:ℝ)/168755200)*ClassicalSixthBranch.v ((606092627:ℝ)/168755200)/ClassicalSixthBranch.r = (133428569455097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1190
  · change upperPayment 1191 ≤ upperValue ((point split endpoint 4096 1191+point split endpoint 4096 1192)/2)
    have hp : upperPayment 1191 = (345530387209:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1191+point split endpoint 4096 1192)/2 = (606117777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606117777:ℝ)/168755200)*ClassicalSixthBranch.v ((606117777:ℝ)/168755200)/ClassicalSixthBranch.r = (133404962807985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1191
  · change upperPayment 1192 ≤ upperValue ((point split endpoint 4096 1192+point split endpoint 4096 1193)/2)
    have hp : upperPayment 1192 = (345451536861:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1192+point split endpoint 4096 1193)/2 = (606142927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606142927:ℝ)/168755200)*ClassicalSixthBranch.v ((606142927:ℝ)/168755200)/ClassicalSixthBranch.r = (133381358184945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1192
  · change upperPayment 1193 ≤ upperValue ((point split endpoint 4096 1193+point split endpoint 4096 1194)/2)
    have hp : upperPayment 1193 = (345372663852:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1193+point split endpoint 4096 1194)/2 = (606168077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606168077:ℝ)/168755200)*ClassicalSixthBranch.v ((606168077:ℝ)/168755200)/ClassicalSixthBranch.r = (133357755585977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1193
  · change upperPayment 1194 ≤ upperValue ((point split endpoint 4096 1194+point split endpoint 4096 1195)/2)
    have hp : upperPayment 1194 = (345293768180:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1194+point split endpoint 4096 1195)/2 = (606193227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606193227:ℝ)/168755200)*ClassicalSixthBranch.v ((606193227:ℝ)/168755200)/ClassicalSixthBranch.r = (133334155011081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1194
  · change upperPayment 1195 ≤ upperValue ((point split endpoint 4096 1195+point split endpoint 4096 1196)/2)
    have hp : upperPayment 1195 = (345214849841:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1195+point split endpoint 4096 1196)/2 = (606218377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606218377:ℝ)/168755200)*ClassicalSixthBranch.v ((606218377:ℝ)/168755200)/ClassicalSixthBranch.r = (133310556460257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1195
  · change upperPayment 1196 ≤ upperValue ((point split endpoint 4096 1196+point split endpoint 4096 1197)/2)
    have hp : upperPayment 1196 = (345135908831:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1196+point split endpoint 4096 1197)/2 = (606243527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606243527:ℝ)/168755200)*ClassicalSixthBranch.v ((606243527:ℝ)/168755200)/ClassicalSixthBranch.r = (133286959933505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1196
  · change upperPayment 1197 ≤ upperValue ((point split endpoint 4096 1197+point split endpoint 4096 1198)/2)
    have hp : upperPayment 1197 = (345056945146:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1197+point split endpoint 4096 1198)/2 = (606268677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606268677:ℝ)/168755200)*ClassicalSixthBranch.v ((606268677:ℝ)/168755200)/ClassicalSixthBranch.r = (133263365430825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1197
  · change upperPayment 1198 ≤ upperValue ((point split endpoint 4096 1198+point split endpoint 4096 1199)/2)
    have hp : upperPayment 1198 = (344977958783:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1198+point split endpoint 4096 1199)/2 = (606293827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606293827:ℝ)/168755200)*ClassicalSixthBranch.v ((606293827:ℝ)/168755200)/ClassicalSixthBranch.r = (133239772952217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1198
  · change upperPayment 1199 ≤ upperValue ((point split endpoint 4096 1199+point split endpoint 4096 1200)/2)
    have hp : upperPayment 1199 = (344898949737:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1199+point split endpoint 4096 1200)/2 = (606318977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606318977:ℝ)/168755200)*ClassicalSixthBranch.v ((606318977:ℝ)/168755200)/ClassicalSixthBranch.r = (133216182497681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1199
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_074
