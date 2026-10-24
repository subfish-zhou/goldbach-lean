import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints071
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_071 (j : Fin 16) : upperPayment (16*71+j.val) ≤
    upperValue ((point split endpoint 4096 (16*71+j.val)+point split endpoint 4096 (16*71+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1136 ≤ upperValue ((point split endpoint 4096 1136+point split endpoint 4096 1137)/2)
    have hp : upperPayment 1136 = (349832368099:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1136+point split endpoint 4096 1137)/2 = (5871209:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5871209:ℝ)/1638400)*ClassicalSixthBranch.v ((5871209:ℝ)/1638400)/ClassicalSixthBranch.r = (1307828486855:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1136
  · change upperPayment 1137 ≤ upperValue ((point split endpoint 4096 1137+point split endpoint 4096 1138)/2)
    have hp : upperPayment 1137 = (349754758376:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1137+point split endpoint 4096 1138)/2 = (604759677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604759677:ℝ)/168755200)*ClassicalSixthBranch.v ((604759677:ℝ)/168755200)/ClassicalSixthBranch.r = (134682618199065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1137
  · change upperPayment 1138 ≤ upperValue ((point split endpoint 4096 1138+point split endpoint 4096 1139)/2)
    have hp : upperPayment 1138 = (349677126195:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1138+point split endpoint 4096 1139)/2 = (604784827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604784827:ℝ)/168755200)*ClassicalSixthBranch.v ((604784827:ℝ)/168755200)/ClassicalSixthBranch.r = (134658904276137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1138
  · change upperPayment 1139 ≤ upperValue ((point split endpoint 4096 1139+point split endpoint 4096 1140)/2)
    have hp : upperPayment 1139 = (349599471552:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1139+point split endpoint 4096 1140)/2 = (604809977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604809977:ℝ)/168755200)*ClassicalSixthBranch.v ((604809977:ℝ)/168755200)/ClassicalSixthBranch.r = (134635192377281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1139
  · change upperPayment 1140 ≤ upperValue ((point split endpoint 4096 1140+point split endpoint 4096 1141)/2)
    have hp : upperPayment 1140 = (349521794443:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1140+point split endpoint 4096 1141)/2 = (604835127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604835127:ℝ)/168755200)*ClassicalSixthBranch.v ((604835127:ℝ)/168755200)/ClassicalSixthBranch.r = (134611482502497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1140
  · change upperPayment 1141 ≤ upperValue ((point split endpoint 4096 1141+point split endpoint 4096 1142)/2)
    have hp : upperPayment 1141 = (349444094865:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1141+point split endpoint 4096 1142)/2 = (604860277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604860277:ℝ)/168755200)*ClassicalSixthBranch.v ((604860277:ℝ)/168755200)/ClassicalSixthBranch.r = (134587774651785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1141
  · change upperPayment 1142 ≤ upperValue ((point split endpoint 4096 1142+point split endpoint 4096 1143)/2)
    have hp : upperPayment 1142 = (349366372815:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1142+point split endpoint 4096 1143)/2 = (604885427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604885427:ℝ)/168755200)*ClassicalSixthBranch.v ((604885427:ℝ)/168755200)/ClassicalSixthBranch.r = (134564068825145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1142
  · change upperPayment 1143 ≤ upperValue ((point split endpoint 4096 1143+point split endpoint 4096 1144)/2)
    have hp : upperPayment 1143 = (349288628288:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1143+point split endpoint 4096 1144)/2 = (604910577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604910577:ℝ)/168755200)*ClassicalSixthBranch.v ((604910577:ℝ)/168755200)/ClassicalSixthBranch.r = (134540365022577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1143
  · change upperPayment 1144 ≤ upperValue ((point split endpoint 4096 1144+point split endpoint 4096 1145)/2)
    have hp : upperPayment 1144 = (349210861280:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1144+point split endpoint 4096 1145)/2 = (604935727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604935727:ℝ)/168755200)*ClassicalSixthBranch.v ((604935727:ℝ)/168755200)/ClassicalSixthBranch.r = (134516663244081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1144
  · change upperPayment 1145 ≤ upperValue ((point split endpoint 4096 1145+point split endpoint 4096 1146)/2)
    have hp : upperPayment 1145 = (349133071790:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1145+point split endpoint 4096 1146)/2 = (604960877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604960877:ℝ)/168755200)*ClassicalSixthBranch.v ((604960877:ℝ)/168755200)/ClassicalSixthBranch.r = (134492963489657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1145
  · change upperPayment 1146 ≤ upperValue ((point split endpoint 4096 1146+point split endpoint 4096 1147)/2)
    have hp : upperPayment 1146 = (349055259811:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1146+point split endpoint 4096 1147)/2 = (604986027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((604986027:ℝ)/168755200)*ClassicalSixthBranch.v ((604986027:ℝ)/168755200)/ClassicalSixthBranch.r = (134469265759305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1146
  · change upperPayment 1147 ≤ upperValue ((point split endpoint 4096 1147+point split endpoint 4096 1148)/2)
    have hp : upperPayment 1147 = (348977425342:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1147+point split endpoint 4096 1148)/2 = (605011177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605011177:ℝ)/168755200)*ClassicalSixthBranch.v ((605011177:ℝ)/168755200)/ClassicalSixthBranch.r = (134445570053025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1147
  · change upperPayment 1148 ≤ upperValue ((point split endpoint 4096 1148+point split endpoint 4096 1149)/2)
    have hp : upperPayment 1148 = (348899568379:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1148+point split endpoint 4096 1149)/2 = (605036327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605036327:ℝ)/168755200)*ClassicalSixthBranch.v ((605036327:ℝ)/168755200)/ClassicalSixthBranch.r = (134421876370817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1148
  · change upperPayment 1149 ≤ upperValue ((point split endpoint 4096 1149+point split endpoint 4096 1150)/2)
    have hp : upperPayment 1149 = (348821688917:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1149+point split endpoint 4096 1150)/2 = (605061477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605061477:ℝ)/168755200)*ClassicalSixthBranch.v ((605061477:ℝ)/168755200)/ClassicalSixthBranch.r = (134398184712681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1149
  · change upperPayment 1150 ≤ upperValue ((point split endpoint 4096 1150+point split endpoint 4096 1151)/2)
    have hp : upperPayment 1150 = (348743786953:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1150+point split endpoint 4096 1151)/2 = (605086627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605086627:ℝ)/168755200)*ClassicalSixthBranch.v ((605086627:ℝ)/168755200)/ClassicalSixthBranch.r = (134374495078617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1150
  · change upperPayment 1151 ≤ upperValue ((point split endpoint 4096 1151+point split endpoint 4096 1152)/2)
    have hp : upperPayment 1151 = (348665862483:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1151+point split endpoint 4096 1152)/2 = (605111777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((605111777:ℝ)/168755200)*ClassicalSixthBranch.v ((605111777:ℝ)/168755200)/ClassicalSixthBranch.r = (134350807468625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1151
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_071
