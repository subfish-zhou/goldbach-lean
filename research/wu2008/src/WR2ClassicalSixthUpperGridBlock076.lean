import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints076
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_076 (j : Fin 16) : upperPayment (16*76+j.val) ≤
    upperValue ((point split endpoint 4096 (16*76+j.val)+point split endpoint 4096 (16*76+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1216 ≤ upperValue ((point split endpoint 4096 1216+point split endpoint 4096 1217)/2)
    have hp : upperPayment 1216 = (343552322001:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1216+point split endpoint 4096 1217)/2 = (606746527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606746527:ℝ)/168755200)*ClassicalSixthBranch.v ((606746527:ℝ)/168755200)/ClassicalSixthBranch.r = (132815454453585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1216
  · change upperPayment 1217 ≤ upperValue ((point split endpoint 4096 1217+point split endpoint 4096 1218)/2)
    have hp : upperPayment 1217 = (343472904042:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1217+point split endpoint 4096 1218)/2 = (606771677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606771677:ℝ)/168755200)*ClassicalSixthBranch.v ((606771677:ℝ)/168755200)/ClassicalSixthBranch.r = (132791900432345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1217
  · change upperPayment 1218 ≤ upperValue ((point split endpoint 4096 1218+point split endpoint 4096 1219)/2)
    have hp : upperPayment 1218 = (343393463329:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1218+point split endpoint 4096 1219)/2 = (606796827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606796827:ℝ)/168755200)*ClassicalSixthBranch.v ((606796827:ℝ)/168755200)/ClassicalSixthBranch.r = (132768348435177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1218
  · change upperPayment 1219 ≤ upperValue ((point split endpoint 4096 1219+point split endpoint 4096 1220)/2)
    have hp : upperPayment 1219 = (343313999859:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1219+point split endpoint 4096 1220)/2 = (606821977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606821977:ℝ)/168755200)*ClassicalSixthBranch.v ((606821977:ℝ)/168755200)/ClassicalSixthBranch.r = (132744798462081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1219
  · change upperPayment 1220 ≤ upperValue ((point split endpoint 4096 1220+point split endpoint 4096 1221)/2)
    have hp : upperPayment 1220 = (343234513629:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1220+point split endpoint 4096 1221)/2 = (606847127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606847127:ℝ)/168755200)*ClassicalSixthBranch.v ((606847127:ℝ)/168755200)/ClassicalSixthBranch.r = (132721250513057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1220
  · change upperPayment 1221 ≤ upperValue ((point split endpoint 4096 1221+point split endpoint 4096 1222)/2)
    have hp : upperPayment 1221 = (343155004635:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1221+point split endpoint 4096 1222)/2 = (606872277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606872277:ℝ)/168755200)*ClassicalSixthBranch.v ((606872277:ℝ)/168755200)/ClassicalSixthBranch.r = (132697704588105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1221
  · change upperPayment 1222 ≤ upperValue ((point split endpoint 4096 1222+point split endpoint 4096 1223)/2)
    have hp : upperPayment 1222 = (343075472873:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1222+point split endpoint 4096 1223)/2 = (606897427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606897427:ℝ)/168755200)*ClassicalSixthBranch.v ((606897427:ℝ)/168755200)/ClassicalSixthBranch.r = (132674160687225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1222
  · change upperPayment 1223 ≤ upperValue ((point split endpoint 4096 1223+point split endpoint 4096 1224)/2)
    have hp : upperPayment 1223 = (342995918339:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1223+point split endpoint 4096 1224)/2 = (606922577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606922577:ℝ)/168755200)*ClassicalSixthBranch.v ((606922577:ℝ)/168755200)/ClassicalSixthBranch.r = (132650618810417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1223
  · change upperPayment 1224 ≤ upperValue ((point split endpoint 4096 1224+point split endpoint 4096 1225)/2)
    have hp : upperPayment 1224 = (342916341029:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1224+point split endpoint 4096 1225)/2 = (606947727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606947727:ℝ)/168755200)*ClassicalSixthBranch.v ((606947727:ℝ)/168755200)/ClassicalSixthBranch.r = (132627078957681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1224
  · change upperPayment 1225 ≤ upperValue ((point split endpoint 4096 1225+point split endpoint 4096 1226)/2)
    have hp : upperPayment 1225 = (342836740941:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1225+point split endpoint 4096 1226)/2 = (606972877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606972877:ℝ)/168755200)*ClassicalSixthBranch.v ((606972877:ℝ)/168755200)/ClassicalSixthBranch.r = (132603541129017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1225
  · change upperPayment 1226 ≤ upperValue ((point split endpoint 4096 1226+point split endpoint 4096 1227)/2)
    have hp : upperPayment 1226 = (342757118069:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1226+point split endpoint 4096 1227)/2 = (606998027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((606998027:ℝ)/168755200)*ClassicalSixthBranch.v ((606998027:ℝ)/168755200)/ClassicalSixthBranch.r = (132580005324425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1226
  · change upperPayment 1227 ≤ upperValue ((point split endpoint 4096 1227+point split endpoint 4096 1228)/2)
    have hp : upperPayment 1227 = (342677472410:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1227+point split endpoint 4096 1228)/2 = (607023177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607023177:ℝ)/168755200)*ClassicalSixthBranch.v ((607023177:ℝ)/168755200)/ClassicalSixthBranch.r = (132556471543905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1227
  · change upperPayment 1228 ≤ upperValue ((point split endpoint 4096 1228+point split endpoint 4096 1229)/2)
    have hp : upperPayment 1228 = (342597803961:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1228+point split endpoint 4096 1229)/2 = (607048327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607048327:ℝ)/168755200)*ClassicalSixthBranch.v ((607048327:ℝ)/168755200)/ClassicalSixthBranch.r = (132532939787457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1228
  · change upperPayment 1229 ≤ upperValue ((point split endpoint 4096 1229+point split endpoint 4096 1230)/2)
    have hp : upperPayment 1229 = (342518112718:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1229+point split endpoint 4096 1230)/2 = (607073477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607073477:ℝ)/168755200)*ClassicalSixthBranch.v ((607073477:ℝ)/168755200)/ClassicalSixthBranch.r = (132509410055081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1229
  · change upperPayment 1230 ≤ upperValue ((point split endpoint 4096 1230+point split endpoint 4096 1231)/2)
    have hp : upperPayment 1230 = (342438398677:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1230+point split endpoint 4096 1231)/2 = (607098627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607098627:ℝ)/168755200)*ClassicalSixthBranch.v ((607098627:ℝ)/168755200)/ClassicalSixthBranch.r = (132485882346777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1230
  · change upperPayment 1231 ≤ upperValue ((point split endpoint 4096 1231+point split endpoint 4096 1232)/2)
    have hp : upperPayment 1231 = (342358661834:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1231+point split endpoint 4096 1232)/2 = (607123777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607123777:ℝ)/168755200)*ClassicalSixthBranch.v ((607123777:ℝ)/168755200)/ClassicalSixthBranch.r = (132462356662545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1231
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_076
