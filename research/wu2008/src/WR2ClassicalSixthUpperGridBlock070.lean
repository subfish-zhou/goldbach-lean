import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints070
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_070 (j : Fin 16) : upperPayment (16*70+j.val) ≤
    upperValue ((point split endpoint 4096 (16*70+j.val)+point split endpoint 4096 (16*70+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1120 ≤ upperValue ((point split endpoint 4096 1120+point split endpoint 4096 1121)/2)
    have hp : upperPayment 1120 = (351071072284:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1120+point split endpoint 4096 1121)/2 = (604332127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604332127:ℝ)/168755200)*ClassicalSixthBranch.v ((604332127:ℝ)/168755200)/ClassicalSixthBranch.r = (135086064571857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1120
  · change upperPayment 1121 ≤ upperValue ((point split endpoint 4096 1121+point split endpoint 4096 1122)/2)
    have hp : upperPayment 1121 = (350993821402:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1121+point split endpoint 4096 1122)/2 = (604357277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604357277:ℝ)/168755200)*ClassicalSixthBranch.v ((604357277:ℝ)/168755200)/ClassicalSixthBranch.r = (135062316239705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1121
  · change upperPayment 1122 ≤ upperValue ((point split endpoint 4096 1122+point split endpoint 4096 1123)/2)
    have hp : upperPayment 1122 = (350916548121:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1122+point split endpoint 4096 1123)/2 = (604382427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604382427:ℝ)/168755200)*ClassicalSixthBranch.v ((604382427:ℝ)/168755200)/ClassicalSixthBranch.r = (135038569931625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1122
  · change upperPayment 1123 ≤ upperValue ((point split endpoint 4096 1123+point split endpoint 4096 1124)/2)
    have hp : upperPayment 1123 = (350839252435:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1123+point split endpoint 4096 1124)/2 = (604407577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604407577:ℝ)/168755200)*ClassicalSixthBranch.v ((604407577:ℝ)/168755200)/ClassicalSixthBranch.r = (135014825647617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1123
  · change upperPayment 1124 ≤ upperValue ((point split endpoint 4096 1124+point split endpoint 4096 1125)/2)
    have hp : upperPayment 1124 = (350761934341:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1124+point split endpoint 4096 1125)/2 = (604432727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604432727:ℝ)/168755200)*ClassicalSixthBranch.v ((604432727:ℝ)/168755200)/ClassicalSixthBranch.r = (134991083387681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1124
  · change upperPayment 1125 ≤ upperValue ((point split endpoint 4096 1125+point split endpoint 4096 1126)/2)
    have hp : upperPayment 1125 = (350684593836:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1125+point split endpoint 4096 1126)/2 = (604457877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604457877:ℝ)/168755200)*ClassicalSixthBranch.v ((604457877:ℝ)/168755200)/ClassicalSixthBranch.r = (134967343151817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1125
  · change upperPayment 1126 ≤ upperValue ((point split endpoint 4096 1126+point split endpoint 4096 1127)/2)
    have hp : upperPayment 1126 = (350607230916:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1126+point split endpoint 4096 1127)/2 = (604483027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604483027:ℝ)/168755200)*ClassicalSixthBranch.v ((604483027:ℝ)/168755200)/ClassicalSixthBranch.r = (134943604940025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1126
  · change upperPayment 1127 ≤ upperValue ((point split endpoint 4096 1127+point split endpoint 4096 1128)/2)
    have hp : upperPayment 1127 = (350529845578:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1127+point split endpoint 4096 1128)/2 = (604508177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604508177:ℝ)/168755200)*ClassicalSixthBranch.v ((604508177:ℝ)/168755200)/ClassicalSixthBranch.r = (134919868752305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1127
  · change upperPayment 1128 ≤ upperValue ((point split endpoint 4096 1128+point split endpoint 4096 1129)/2)
    have hp : upperPayment 1128 = (350452437817:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1128+point split endpoint 4096 1129)/2 = (604533327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604533327:ℝ)/168755200)*ClassicalSixthBranch.v ((604533327:ℝ)/168755200)/ClassicalSixthBranch.r = (134896134588657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1128
  · change upperPayment 1129 ≤ upperValue ((point split endpoint 4096 1129+point split endpoint 4096 1130)/2)
    have hp : upperPayment 1129 = (350375007630:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1129+point split endpoint 4096 1130)/2 = (604558477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604558477:ℝ)/168755200)*ClassicalSixthBranch.v ((604558477:ℝ)/168755200)/ClassicalSixthBranch.r = (134872402449081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1129
  · change upperPayment 1130 ≤ upperValue ((point split endpoint 4096 1130+point split endpoint 4096 1131)/2)
    have hp : upperPayment 1130 = (350297555014:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1130+point split endpoint 4096 1131)/2 = (604583627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604583627:ℝ)/168755200)*ClassicalSixthBranch.v ((604583627:ℝ)/168755200)/ClassicalSixthBranch.r = (134848672333577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1130
  · change upperPayment 1131 ≤ upperValue ((point split endpoint 4096 1131+point split endpoint 4096 1132)/2)
    have hp : upperPayment 1131 = (350220079965:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1131+point split endpoint 4096 1132)/2 = (604608777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604608777:ℝ)/168755200)*ClassicalSixthBranch.v ((604608777:ℝ)/168755200)/ClassicalSixthBranch.r = (134824944242145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1131
  · change upperPayment 1132 ≤ upperValue ((point split endpoint 4096 1132+point split endpoint 4096 1133)/2)
    have hp : upperPayment 1132 = (350142582480:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1132+point split endpoint 4096 1133)/2 = (604633927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604633927:ℝ)/168755200)*ClassicalSixthBranch.v ((604633927:ℝ)/168755200)/ClassicalSixthBranch.r = (134801218174785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1132
  · change upperPayment 1133 ≤ upperValue ((point split endpoint 4096 1133+point split endpoint 4096 1134)/2)
    have hp : upperPayment 1133 = (350065062554:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1133+point split endpoint 4096 1134)/2 = (604659077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604659077:ℝ)/168755200)*ClassicalSixthBranch.v ((604659077:ℝ)/168755200)/ClassicalSixthBranch.r = (134777494131497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1133
  · change upperPayment 1134 ≤ upperValue ((point split endpoint 4096 1134+point split endpoint 4096 1135)/2)
    have hp : upperPayment 1134 = (349987520184:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1134+point split endpoint 4096 1135)/2 = (604684227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604684227:ℝ)/168755200)*ClassicalSixthBranch.v ((604684227:ℝ)/168755200)/ClassicalSixthBranch.r = (134753772112281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1134
  · change upperPayment 1135 ≤ upperValue ((point split endpoint 4096 1135+point split endpoint 4096 1136)/2)
    have hp : upperPayment 1135 = (349909955367:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1135+point split endpoint 4096 1136)/2 = (604709377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604709377:ℝ)/168755200)*ClassicalSixthBranch.v ((604709377:ℝ)/168755200)/ClassicalSixthBranch.r = (134730052117137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1135
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_070
