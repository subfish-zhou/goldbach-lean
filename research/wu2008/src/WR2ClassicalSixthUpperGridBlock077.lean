import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints077
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_077 (j : Fin 16) : upperPayment (16*77+j.val) ≤
    upperValue ((point split endpoint 4096 (16*77+j.val)+point split endpoint 4096 (16*77+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1232 ≤ upperValue ((point split endpoint 4096 1232+point split endpoint 4096 1233)/2)
    have hp : upperPayment 1232 = (342278902185:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1232+point split endpoint 4096 1233)/2 = (607148927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607148927:ℝ)/168755200)*ClassicalSixthBranch.v ((607148927:ℝ)/168755200)/ClassicalSixthBranch.r = (132438833002385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1232
  · change upperPayment 1233 ≤ upperValue ((point split endpoint 4096 1233+point split endpoint 4096 1234)/2)
    have hp : upperPayment 1233 = (342199119727:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1233+point split endpoint 4096 1234)/2 = (607174077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607174077:ℝ)/168755200)*ClassicalSixthBranch.v ((607174077:ℝ)/168755200)/ClassicalSixthBranch.r = (132415311366297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1233
  · change upperPayment 1234 ≤ upperValue ((point split endpoint 4096 1234+point split endpoint 4096 1235)/2)
    have hp : upperPayment 1234 = (342119314456:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1234+point split endpoint 4096 1235)/2 = (607199227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607199227:ℝ)/168755200)*ClassicalSixthBranch.v ((607199227:ℝ)/168755200)/ClassicalSixthBranch.r = (132391791754281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1234
  · change upperPayment 1235 ≤ upperValue ((point split endpoint 4096 1235+point split endpoint 4096 1236)/2)
    have hp : upperPayment 1235 = (342039486368:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1235+point split endpoint 4096 1236)/2 = (607224377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607224377:ℝ)/168755200)*ClassicalSixthBranch.v ((607224377:ℝ)/168755200)/ClassicalSixthBranch.r = (132368274166337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1235
  · change upperPayment 1236 ≤ upperValue ((point split endpoint 4096 1236+point split endpoint 4096 1237)/2)
    have hp : upperPayment 1236 = (341959635459:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1236+point split endpoint 4096 1237)/2 = (607249527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607249527:ℝ)/168755200)*ClassicalSixthBranch.v ((607249527:ℝ)/168755200)/ClassicalSixthBranch.r = (132344758602465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1236
  · change upperPayment 1237 ≤ upperValue ((point split endpoint 4096 1237+point split endpoint 4096 1238)/2)
    have hp : upperPayment 1237 = (341879761726:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1237+point split endpoint 4096 1238)/2 = (607274677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607274677:ℝ)/168755200)*ClassicalSixthBranch.v ((607274677:ℝ)/168755200)/ClassicalSixthBranch.r = (132321245062665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1237
  · change upperPayment 1238 ≤ upperValue ((point split endpoint 4096 1238+point split endpoint 4096 1239)/2)
    have hp : upperPayment 1238 = (341799865164:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1238+point split endpoint 4096 1239)/2 = (607299827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607299827:ℝ)/168755200)*ClassicalSixthBranch.v ((607299827:ℝ)/168755200)/ClassicalSixthBranch.r = (132297733546937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1238
  · change upperPayment 1239 ≤ upperValue ((point split endpoint 4096 1239+point split endpoint 4096 1240)/2)
    have hp : upperPayment 1239 = (341719945771:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1239+point split endpoint 4096 1240)/2 = (5896359:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5896359:ℝ)/1638400)*ClassicalSixthBranch.v ((5896359:ℝ)/1638400)/ClassicalSixthBranch.r = (1284215767527:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1239
  · change upperPayment 1240 ≤ upperValue ((point split endpoint 4096 1240+point split endpoint 4096 1241)/2)
    have hp : upperPayment 1240 = (341640003542:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1240+point split endpoint 4096 1241)/2 = (607350127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607350127:ℝ)/168755200)*ClassicalSixthBranch.v ((607350127:ℝ)/168755200)/ClassicalSixthBranch.r = (132250716587697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1240
  · change upperPayment 1241 ≤ upperValue ((point split endpoint 4096 1241+point split endpoint 4096 1242)/2)
    have hp : upperPayment 1241 = (341560038473:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1241+point split endpoint 4096 1242)/2 = (607375277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607375277:ℝ)/168755200)*ClassicalSixthBranch.v ((607375277:ℝ)/168755200)/ClassicalSixthBranch.r = (132227211144185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1241
  · change upperPayment 1242 ≤ upperValue ((point split endpoint 4096 1242+point split endpoint 4096 1243)/2)
    have hp : upperPayment 1242 = (341480050561:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1242+point split endpoint 4096 1243)/2 = (607400427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607400427:ℝ)/168755200)*ClassicalSixthBranch.v ((607400427:ℝ)/168755200)/ClassicalSixthBranch.r = (132203707724745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1242
  · change upperPayment 1243 ≤ upperValue ((point split endpoint 4096 1243+point split endpoint 4096 1244)/2)
    have hp : upperPayment 1243 = (341400039801:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1243+point split endpoint 4096 1244)/2 = (607425577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607425577:ℝ)/168755200)*ClassicalSixthBranch.v ((607425577:ℝ)/168755200)/ClassicalSixthBranch.r = (132180206329377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1243
  · change upperPayment 1244 ≤ upperValue ((point split endpoint 4096 1244+point split endpoint 4096 1245)/2)
    have hp : upperPayment 1244 = (341320006191:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1244+point split endpoint 4096 1245)/2 = (607450727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607450727:ℝ)/168755200)*ClassicalSixthBranch.v ((607450727:ℝ)/168755200)/ClassicalSixthBranch.r = (132156706958081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1244
  · change upperPayment 1245 ≤ upperValue ((point split endpoint 4096 1245+point split endpoint 4096 1246)/2)
    have hp : upperPayment 1245 = (341239949726:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1245+point split endpoint 4096 1246)/2 = (607475877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607475877:ℝ)/168755200)*ClassicalSixthBranch.v ((607475877:ℝ)/168755200)/ClassicalSixthBranch.r = (132133209610857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1245
  · change upperPayment 1246 ≤ upperValue ((point split endpoint 4096 1246+point split endpoint 4096 1247)/2)
    have hp : upperPayment 1246 = (341159870403:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1246+point split endpoint 4096 1247)/2 = (607501027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607501027:ℝ)/168755200)*ClassicalSixthBranch.v ((607501027:ℝ)/168755200)/ClassicalSixthBranch.r = (132109714287705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1246
  · change upperPayment 1247 ≤ upperValue ((point split endpoint 4096 1247+point split endpoint 4096 1248)/2)
    have hp : upperPayment 1247 = (341079768217:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1247+point split endpoint 4096 1248)/2 = (607526177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((607526177:ℝ)/168755200)*ClassicalSixthBranch.v ((607526177:ℝ)/168755200)/ClassicalSixthBranch.r = (132086220988625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1247
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_077
