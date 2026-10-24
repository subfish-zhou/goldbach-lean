import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints081
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_081 (j : Fin 16) : upperPayment (16*81+j.val) ≤
    upperValue ((point split endpoint 4096 (16*81+j.val)+point split endpoint 4096 (16*81+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1296 ≤ upperValue ((point split endpoint 4096 1296+point split endpoint 4096 1297)/2)
    have hp : upperPayment 1296 = (337126675387:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1296+point split endpoint 4096 1297)/2 = (608758527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608758527:ℝ)/168755200)*ClassicalSixthBranch.v ((608758527:ℝ)/168755200)/ClassicalSixthBranch.r = (130937528821905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1296
  · change upperPayment 1297 ≤ upperValue ((point split endpoint 4096 1297+point split endpoint 4096 1298)/2)
    have hp : upperPayment 1297 = (337045425215:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1297+point split endpoint 4096 1298)/2 = (608783677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608783677:ℝ)/168755200)*ClassicalSixthBranch.v ((608783677:ℝ)/168755200)/ClassicalSixthBranch.r = (130914136726425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1297
  · change upperPayment 1298 ≤ upperValue ((point split endpoint 4096 1298+point split endpoint 4096 1299)/2)
    have hp : upperPayment 1298 = (336964151985:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1298+point split endpoint 4096 1299)/2 = (608808827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608808827:ℝ)/168755200)*ClassicalSixthBranch.v ((608808827:ℝ)/168755200)/ClassicalSixthBranch.r = (130890746655017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1298
  · change upperPayment 1299 ≤ upperValue ((point split endpoint 4096 1299+point split endpoint 4096 1300)/2)
    have hp : upperPayment 1299 = (336882855694:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1299+point split endpoint 4096 1300)/2 = (608833977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608833977:ℝ)/168755200)*ClassicalSixthBranch.v ((608833977:ℝ)/168755200)/ClassicalSixthBranch.r = (130867358607681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1299
  · change upperPayment 1300 ≤ upperValue ((point split endpoint 4096 1300+point split endpoint 4096 1301)/2)
    have hp : upperPayment 1300 = (336801536337:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1300+point split endpoint 4096 1301)/2 = (608859127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608859127:ℝ)/168755200)*ClassicalSixthBranch.v ((608859127:ℝ)/168755200)/ClassicalSixthBranch.r = (130843972584417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1300
  · change upperPayment 1301 ≤ upperValue ((point split endpoint 4096 1301+point split endpoint 4096 1302)/2)
    have hp : upperPayment 1301 = (336720193911:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1301+point split endpoint 4096 1302)/2 = (608884277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608884277:ℝ)/168755200)*ClassicalSixthBranch.v ((608884277:ℝ)/168755200)/ClassicalSixthBranch.r = (130820588585225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1301
  · change upperPayment 1302 ≤ upperValue ((point split endpoint 4096 1302+point split endpoint 4096 1303)/2)
    have hp : upperPayment 1302 = (336638828411:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1302+point split endpoint 4096 1303)/2 = (608909427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608909427:ℝ)/168755200)*ClassicalSixthBranch.v ((608909427:ℝ)/168755200)/ClassicalSixthBranch.r = (130797206610105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1302
  · change upperPayment 1303 ≤ upperValue ((point split endpoint 4096 1303+point split endpoint 4096 1304)/2)
    have hp : upperPayment 1303 = (336557439835:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1303+point split endpoint 4096 1304)/2 = (608934577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608934577:ℝ)/168755200)*ClassicalSixthBranch.v ((608934577:ℝ)/168755200)/ClassicalSixthBranch.r = (130773826659057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1303
  · change upperPayment 1304 ≤ upperValue ((point split endpoint 4096 1304+point split endpoint 4096 1305)/2)
    have hp : upperPayment 1304 = (336476028177:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1304+point split endpoint 4096 1305)/2 = (608959727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608959727:ℝ)/168755200)*ClassicalSixthBranch.v ((608959727:ℝ)/168755200)/ClassicalSixthBranch.r = (130750448732081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1304
  · change upperPayment 1305 ≤ upperValue ((point split endpoint 4096 1305+point split endpoint 4096 1306)/2)
    have hp : upperPayment 1305 = (336394593433:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1305+point split endpoint 4096 1306)/2 = (608984877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((608984877:ℝ)/168755200)*ClassicalSixthBranch.v ((608984877:ℝ)/168755200)/ClassicalSixthBranch.r = (130727072829177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1305
  · change upperPayment 1306 ≤ upperValue ((point split endpoint 4096 1306+point split endpoint 4096 1307)/2)
    have hp : upperPayment 1306 = (336313135601:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1306+point split endpoint 4096 1307)/2 = (609010027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609010027:ℝ)/168755200)*ClassicalSixthBranch.v ((609010027:ℝ)/168755200)/ClassicalSixthBranch.r = (130703698950345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1306
  · change upperPayment 1307 ≤ upperValue ((point split endpoint 4096 1307+point split endpoint 4096 1308)/2)
    have hp : upperPayment 1307 = (336231654677:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1307+point split endpoint 4096 1308)/2 = (609035177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609035177:ℝ)/168755200)*ClassicalSixthBranch.v ((609035177:ℝ)/168755200)/ClassicalSixthBranch.r = (130680327095585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1307
  · change upperPayment 1308 ≤ upperValue ((point split endpoint 4096 1308+point split endpoint 4096 1309)/2)
    have hp : upperPayment 1308 = (336150150655:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1308+point split endpoint 4096 1309)/2 = (609060327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609060327:ℝ)/168755200)*ClassicalSixthBranch.v ((609060327:ℝ)/168755200)/ClassicalSixthBranch.r = (130656957264897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1308
  · change upperPayment 1309 ≤ upperValue ((point split endpoint 4096 1309+point split endpoint 4096 1310)/2)
    have hp : upperPayment 1309 = (336068623533:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1309+point split endpoint 4096 1310)/2 = (609085477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609085477:ℝ)/168755200)*ClassicalSixthBranch.v ((609085477:ℝ)/168755200)/ClassicalSixthBranch.r = (130633589458281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1309
  · change upperPayment 1310 ≤ upperValue ((point split endpoint 4096 1310+point split endpoint 4096 1311)/2)
    have hp : upperPayment 1310 = (335987073307:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1310+point split endpoint 4096 1311)/2 = (609110627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609110627:ℝ)/168755200)*ClassicalSixthBranch.v ((609110627:ℝ)/168755200)/ClassicalSixthBranch.r = (130610223675737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1310
  · change upperPayment 1311 ≤ upperValue ((point split endpoint 4096 1311+point split endpoint 4096 1312)/2)
    have hp : upperPayment 1311 = (335905499972:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1311+point split endpoint 4096 1312)/2 = (609135777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((609135777:ℝ)/168755200)*ClassicalSixthBranch.v ((609135777:ℝ)/168755200)/ClassicalSixthBranch.r = (130586859917265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1311
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_081
