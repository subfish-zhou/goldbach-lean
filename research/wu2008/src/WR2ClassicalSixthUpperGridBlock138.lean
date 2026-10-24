import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints138
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_138 (j : Fin 16) : upperPayment (16*138+j.val) ≤
    upperValue ((point split endpoint 4096 (16*138+j.val)+point split endpoint 4096 (16*138+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2208 ≤ upperValue ((point split endpoint 4096 2208+point split endpoint 4096 2209)/2)
    have hp : upperPayment 2208 = (252909547780:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2208+point split endpoint 4096 2209)/2 = (631695327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631695327:ℝ)/168755200)*ClassicalSixthBranch.v ((631695327:ℝ)/168755200)/ClassicalSixthBranch.r = (110444769638097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2208
  · change upperPayment 2209 ≤ upperValue ((point split endpoint 4096 2209+point split endpoint 4096 2210)/2)
    have hp : upperPayment 2209 = (252805435359:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2209+point split endpoint 4096 2210)/2 = (631720477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631720477:ℝ)/168755200)*ClassicalSixthBranch.v ((631720477:ℝ)/168755200)/ClassicalSixthBranch.r = (110423223496281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2209
  · change upperPayment 2210 ≤ upperValue ((point split endpoint 4096 2210+point split endpoint 4096 2211)/2)
    have hp : upperPayment 2210 = (252701295589:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2210+point split endpoint 4096 2211)/2 = (631745627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631745627:ℝ)/168755200)*ClassicalSixthBranch.v ((631745627:ℝ)/168755200)/ClassicalSixthBranch.r = (110401679378537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2210
  · change upperPayment 2211 ≤ upperValue ((point split endpoint 4096 2211+point split endpoint 4096 2212)/2)
    have hp : upperPayment 2211 = (252597128464:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2211+point split endpoint 4096 2212)/2 = (631770777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631770777:ℝ)/168755200)*ClassicalSixthBranch.v ((631770777:ℝ)/168755200)/ClassicalSixthBranch.r = (110380137284865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2211
  · change upperPayment 2212 ≤ upperValue ((point split endpoint 4096 2212+point split endpoint 4096 2213)/2)
    have hp : upperPayment 2212 = (252492933978:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2212+point split endpoint 4096 2213)/2 = (631795927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631795927:ℝ)/168755200)*ClassicalSixthBranch.v ((631795927:ℝ)/168755200)/ClassicalSixthBranch.r = (110358597215265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2212
  · change upperPayment 2213 ≤ upperValue ((point split endpoint 4096 2213+point split endpoint 4096 2214)/2)
    have hp : upperPayment 2213 = (252388712127:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2213+point split endpoint 4096 2214)/2 = (631821077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631821077:ℝ)/168755200)*ClassicalSixthBranch.v ((631821077:ℝ)/168755200)/ClassicalSixthBranch.r = (110337059169737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2213
  · change upperPayment 2214 ≤ upperValue ((point split endpoint 4096 2214+point split endpoint 4096 2215)/2)
    have hp : upperPayment 2214 = (252284462904:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2214+point split endpoint 4096 2215)/2 = (631846227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631846227:ℝ)/168755200)*ClassicalSixthBranch.v ((631846227:ℝ)/168755200)/ClassicalSixthBranch.r = (110315523148281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2214
  · change upperPayment 2215 ≤ upperValue ((point split endpoint 4096 2215+point split endpoint 4096 2216)/2)
    have hp : upperPayment 2215 = (252180186303:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2215+point split endpoint 4096 2216)/2 = (631871377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631871377:ℝ)/168755200)*ClassicalSixthBranch.v ((631871377:ℝ)/168755200)/ClassicalSixthBranch.r = (110293989150897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2215
  · change upperPayment 2216 ≤ upperValue ((point split endpoint 4096 2216+point split endpoint 4096 2217)/2)
    have hp : upperPayment 2216 = (252075882319:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2216+point split endpoint 4096 2217)/2 = (631896527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631896527:ℝ)/168755200)*ClassicalSixthBranch.v ((631896527:ℝ)/168755200)/ClassicalSixthBranch.r = (110272457177585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2216
  · change upperPayment 2217 ≤ upperValue ((point split endpoint 4096 2217+point split endpoint 4096 2218)/2)
    have hp : upperPayment 2217 = (251971550947:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2217+point split endpoint 4096 2218)/2 = (631921677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631921677:ℝ)/168755200)*ClassicalSixthBranch.v ((631921677:ℝ)/168755200)/ClassicalSixthBranch.r = (110250927228345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2217
  · change upperPayment 2218 ≤ upperValue ((point split endpoint 4096 2218+point split endpoint 4096 2219)/2)
    have hp : upperPayment 2218 = (251867192180:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2218+point split endpoint 4096 2219)/2 = (631946827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631946827:ℝ)/168755200)*ClassicalSixthBranch.v ((631946827:ℝ)/168755200)/ClassicalSixthBranch.r = (110229399303177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2218
  · change upperPayment 2219 ≤ upperValue ((point split endpoint 4096 2219+point split endpoint 4096 2220)/2)
    have hp : upperPayment 2219 = (251762806014:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2219+point split endpoint 4096 2220)/2 = (631971977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631971977:ℝ)/168755200)*ClassicalSixthBranch.v ((631971977:ℝ)/168755200)/ClassicalSixthBranch.r = (110207873402081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2219
  · change upperPayment 2220 ≤ upperValue ((point split endpoint 4096 2220+point split endpoint 4096 2221)/2)
    have hp : upperPayment 2220 = (251658392442:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2220+point split endpoint 4096 2221)/2 = (631997127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((631997127:ℝ)/168755200)*ClassicalSixthBranch.v ((631997127:ℝ)/168755200)/ClassicalSixthBranch.r = (110186349525057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2220
  · change upperPayment 2221 ≤ upperValue ((point split endpoint 4096 2221+point split endpoint 4096 2222)/2)
    have hp : upperPayment 2221 = (251553951458:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2221+point split endpoint 4096 2222)/2 = (632022277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632022277:ℝ)/168755200)*ClassicalSixthBranch.v ((632022277:ℝ)/168755200)/ClassicalSixthBranch.r = (110164827672105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2221
  · change upperPayment 2222 ≤ upperValue ((point split endpoint 4096 2222+point split endpoint 4096 2223)/2)
    have hp : upperPayment 2222 = (251449483058:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2222+point split endpoint 4096 2223)/2 = (632047427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632047427:ℝ)/168755200)*ClassicalSixthBranch.v ((632047427:ℝ)/168755200)/ClassicalSixthBranch.r = (110143307843225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2222
  · change upperPayment 2223 ≤ upperValue ((point split endpoint 4096 2223+point split endpoint 4096 2224)/2)
    have hp : upperPayment 2223 = (251344987235:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2223+point split endpoint 4096 2224)/2 = (632072577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632072577:ℝ)/168755200)*ClassicalSixthBranch.v ((632072577:ℝ)/168755200)/ClassicalSixthBranch.r = (110121790038417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2223
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_138
