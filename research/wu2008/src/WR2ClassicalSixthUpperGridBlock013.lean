import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints013
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_013 (j : Fin 16) : upperPayment (16*13+j.val) ≤
    upperValue ((point split endpoint 4096 (16*13+j.val)+point split endpoint 4096 (16*13+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 208 ≤ upperValue ((point split endpoint 4096 208+point split endpoint 4096 209)/2)
    have hp : upperPayment 208 = (412611443190:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 208+point split endpoint 4096 209)/2 = (581395327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581395327:ℝ)/168755200)*ClassicalSixthBranch.v ((581395327:ℝ)/168755200)/ClassicalSixthBranch.r = (157587221342097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_208
  · change upperPayment 209 ≤ upperValue ((point split endpoint 4096 209+point split endpoint 4096 210)/2)
    have hp : upperPayment 209 = (412553308336:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 209+point split endpoint 4096 210)/2 = (5644859:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5644859:ℝ)/1638400)*ClassicalSixthBranch.v ((5644859:ℝ)/1638400)/ClassicalSixthBranch.r = (1529724534527:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_209
  · change upperPayment 210 ≤ upperValue ((point split endpoint 4096 210+point split endpoint 4096 211)/2)
    have hp : upperPayment 210 = (412495153769:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 210+point split endpoint 4096 211)/2 = (581445627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581445627:ℝ)/168755200)*ClassicalSixthBranch.v ((581445627:ℝ)/168755200)/ClassicalSixthBranch.r = (157536034794537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_210
  · change upperPayment 211 ≤ upperValue ((point split endpoint 4096 211+point split endpoint 4096 212)/2)
    have hp : upperPayment 211 = (412436979488:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 211+point split endpoint 4096 212)/2 = (581470777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581470777:ℝ)/168755200)*ClassicalSixthBranch.v ((581470777:ℝ)/168755200)/ClassicalSixthBranch.r = (157510444556865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_211
  · change upperPayment 212 ≤ upperValue ((point split endpoint 4096 212+point split endpoint 4096 213)/2)
    have hp : upperPayment 212 = (412378785490:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 212+point split endpoint 4096 213)/2 = (581495927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581495927:ℝ)/168755200)*ClassicalSixthBranch.v ((581495927:ℝ)/168755200)/ClassicalSixthBranch.r = (157484856343265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_212
  · change upperPayment 213 ≤ upperValue ((point split endpoint 4096 213+point split endpoint 4096 214)/2)
    have hp : upperPayment 213 = (412320571773:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 213+point split endpoint 4096 214)/2 = (581521077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581521077:ℝ)/168755200)*ClassicalSixthBranch.v ((581521077:ℝ)/168755200)/ClassicalSixthBranch.r = (157459270153737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_213
  · change upperPayment 214 ≤ upperValue ((point split endpoint 4096 214+point split endpoint 4096 215)/2)
    have hp : upperPayment 214 = (412262338333:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 214+point split endpoint 4096 215)/2 = (581546227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581546227:ℝ)/168755200)*ClassicalSixthBranch.v ((581546227:ℝ)/168755200)/ClassicalSixthBranch.r = (157433685988281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_214
  · change upperPayment 215 ≤ upperValue ((point split endpoint 4096 215+point split endpoint 4096 216)/2)
    have hp : upperPayment 215 = (412204085170:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 215+point split endpoint 4096 216)/2 = (581571377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581571377:ℝ)/168755200)*ClassicalSixthBranch.v ((581571377:ℝ)/168755200)/ClassicalSixthBranch.r = (157408103846897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_215
  · change upperPayment 216 ≤ upperValue ((point split endpoint 4096 216+point split endpoint 4096 217)/2)
    have hp : upperPayment 216 = (412145812281:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 216+point split endpoint 4096 217)/2 = (581596527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581596527:ℝ)/168755200)*ClassicalSixthBranch.v ((581596527:ℝ)/168755200)/ClassicalSixthBranch.r = (157382523729585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_216
  · change upperPayment 217 ≤ upperValue ((point split endpoint 4096 217+point split endpoint 4096 218)/2)
    have hp : upperPayment 217 = (412087519662:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 217+point split endpoint 4096 218)/2 = (581621677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581621677:ℝ)/168755200)*ClassicalSixthBranch.v ((581621677:ℝ)/168755200)/ClassicalSixthBranch.r = (157356945636345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_217
  · change upperPayment 218 ≤ upperValue ((point split endpoint 4096 218+point split endpoint 4096 219)/2)
    have hp : upperPayment 218 = (412029207313:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 218+point split endpoint 4096 219)/2 = (581646827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581646827:ℝ)/168755200)*ClassicalSixthBranch.v ((581646827:ℝ)/168755200)/ClassicalSixthBranch.r = (157331369567177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_218
  · change upperPayment 219 ≤ upperValue ((point split endpoint 4096 219+point split endpoint 4096 220)/2)
    have hp : upperPayment 219 = (411970875230:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 219+point split endpoint 4096 220)/2 = (581671977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581671977:ℝ)/168755200)*ClassicalSixthBranch.v ((581671977:ℝ)/168755200)/ClassicalSixthBranch.r = (157305795522081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_219
  · change upperPayment 220 ≤ upperValue ((point split endpoint 4096 220+point split endpoint 4096 221)/2)
    have hp : upperPayment 220 = (411912523411:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 220+point split endpoint 4096 221)/2 = (581697127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581697127:ℝ)/168755200)*ClassicalSixthBranch.v ((581697127:ℝ)/168755200)/ClassicalSixthBranch.r = (157280223501057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_220
  · change upperPayment 221 ≤ upperValue ((point split endpoint 4096 221+point split endpoint 4096 222)/2)
    have hp : upperPayment 221 = (411854151854:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 221+point split endpoint 4096 222)/2 = (581722277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581722277:ℝ)/168755200)*ClassicalSixthBranch.v ((581722277:ℝ)/168755200)/ClassicalSixthBranch.r = (157254653504105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_221
  · change upperPayment 222 ≤ upperValue ((point split endpoint 4096 222+point split endpoint 4096 223)/2)
    have hp : upperPayment 222 = (411795760557:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 222+point split endpoint 4096 223)/2 = (581747427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581747427:ℝ)/168755200)*ClassicalSixthBranch.v ((581747427:ℝ)/168755200)/ClassicalSixthBranch.r = (157229085531225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_222
  · change upperPayment 223 ≤ upperValue ((point split endpoint 4096 223+point split endpoint 4096 224)/2)
    have hp : upperPayment 223 = (411737349516:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 223+point split endpoint 4096 224)/2 = (581772577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((581772577:ℝ)/168755200)*ClassicalSixthBranch.v ((581772577:ℝ)/168755200)/ClassicalSixthBranch.r = (157203519582417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_223
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_013
