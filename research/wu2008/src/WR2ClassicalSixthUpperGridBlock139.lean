import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints139
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_139 (j : Fin 16) : upperPayment (16*139+j.val) ≤
    upperValue ((point split endpoint 4096 (16*139+j.val)+point split endpoint 4096 (16*139+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2224 ≤ upperValue ((point split endpoint 4096 2224+point split endpoint 4096 2225)/2)
    have hp : upperPayment 2224 = (251240463984:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2224+point split endpoint 4096 2225)/2 = (632097727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632097727:ℝ)/168755200)*ClassicalSixthBranch.v ((632097727:ℝ)/168755200)/ClassicalSixthBranch.r = (110100274257681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2224
  · change upperPayment 2225 ≤ upperValue ((point split endpoint 4096 2225+point split endpoint 4096 2226)/2)
    have hp : upperPayment 2225 = (251135913299:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2225+point split endpoint 4096 2226)/2 = (632122877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632122877:ℝ)/168755200)*ClassicalSixthBranch.v ((632122877:ℝ)/168755200)/ClassicalSixthBranch.r = (110078760501017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2225
  · change upperPayment 2226 ≤ upperValue ((point split endpoint 4096 2226+point split endpoint 4096 2227)/2)
    have hp : upperPayment 2226 = (251031335174:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2226+point split endpoint 4096 2227)/2 = (632148027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632148027:ℝ)/168755200)*ClassicalSixthBranch.v ((632148027:ℝ)/168755200)/ClassicalSixthBranch.r = (110057248768425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2226
  · change upperPayment 2227 ≤ upperValue ((point split endpoint 4096 2227+point split endpoint 4096 2228)/2)
    have hp : upperPayment 2227 = (250926729605:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2227+point split endpoint 4096 2228)/2 = (632173177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632173177:ℝ)/168755200)*ClassicalSixthBranch.v ((632173177:ℝ)/168755200)/ClassicalSixthBranch.r = (110035739059905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2227
  · change upperPayment 2228 ≤ upperValue ((point split endpoint 4096 2228+point split endpoint 4096 2229)/2)
    have hp : upperPayment 2228 = (250822096584:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2228+point split endpoint 4096 2229)/2 = (632198327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632198327:ℝ)/168755200)*ClassicalSixthBranch.v ((632198327:ℝ)/168755200)/ClassicalSixthBranch.r = (110014231375457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2228
  · change upperPayment 2229 ≤ upperValue ((point split endpoint 4096 2229+point split endpoint 4096 2230)/2)
    have hp : upperPayment 2229 = (250717436107:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2229+point split endpoint 4096 2230)/2 = (632223477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632223477:ℝ)/168755200)*ClassicalSixthBranch.v ((632223477:ℝ)/168755200)/ClassicalSixthBranch.r = (109992725715081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2229
  · change upperPayment 2230 ≤ upperValue ((point split endpoint 4096 2230+point split endpoint 4096 2231)/2)
    have hp : upperPayment 2230 = (250612748167:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2230+point split endpoint 4096 2231)/2 = (632248627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632248627:ℝ)/168755200)*ClassicalSixthBranch.v ((632248627:ℝ)/168755200)/ClassicalSixthBranch.r = (109971222078777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2230
  · change upperPayment 2231 ≤ upperValue ((point split endpoint 4096 2231+point split endpoint 4096 2232)/2)
    have hp : upperPayment 2231 = (250508032760:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2231+point split endpoint 4096 2232)/2 = (632273777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632273777:ℝ)/168755200)*ClassicalSixthBranch.v ((632273777:ℝ)/168755200)/ClassicalSixthBranch.r = (109949720466545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2231
  · change upperPayment 2232 ≤ upperValue ((point split endpoint 4096 2232+point split endpoint 4096 2233)/2)
    have hp : upperPayment 2232 = (250403289879:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2232+point split endpoint 4096 2233)/2 = (632298927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632298927:ℝ)/168755200)*ClassicalSixthBranch.v ((632298927:ℝ)/168755200)/ClassicalSixthBranch.r = (109928220878385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2232
  · change upperPayment 2233 ≤ upperValue ((point split endpoint 4096 2233+point split endpoint 4096 2234)/2)
    have hp : upperPayment 2233 = (250298519519:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2233+point split endpoint 4096 2234)/2 = (632324077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632324077:ℝ)/168755200)*ClassicalSixthBranch.v ((632324077:ℝ)/168755200)/ClassicalSixthBranch.r = (109906723314297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2233
  · change upperPayment 2234 ≤ upperValue ((point split endpoint 4096 2234+point split endpoint 4096 2235)/2)
    have hp : upperPayment 2234 = (250193721673:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2234+point split endpoint 4096 2235)/2 = (632349227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632349227:ℝ)/168755200)*ClassicalSixthBranch.v ((632349227:ℝ)/168755200)/ClassicalSixthBranch.r = (109885227774281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2234
  · change upperPayment 2235 ≤ upperValue ((point split endpoint 4096 2235+point split endpoint 4096 2236)/2)
    have hp : upperPayment 2235 = (250088896338:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2235+point split endpoint 4096 2236)/2 = (632374377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632374377:ℝ)/168755200)*ClassicalSixthBranch.v ((632374377:ℝ)/168755200)/ClassicalSixthBranch.r = (109863734258337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2235
  · change upperPayment 2236 ≤ upperValue ((point split endpoint 4096 2236+point split endpoint 4096 2237)/2)
    have hp : upperPayment 2236 = (249984043505:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2236+point split endpoint 4096 2237)/2 = (632399527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632399527:ℝ)/168755200)*ClassicalSixthBranch.v ((632399527:ℝ)/168755200)/ClassicalSixthBranch.r = (109842242766465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2236
  · change upperPayment 2237 ≤ upperValue ((point split endpoint 4096 2237+point split endpoint 4096 2238)/2)
    have hp : upperPayment 2237 = (249879163171:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2237+point split endpoint 4096 2238)/2 = (632424677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632424677:ℝ)/168755200)*ClassicalSixthBranch.v ((632424677:ℝ)/168755200)/ClassicalSixthBranch.r = (109820753298665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2237
  · change upperPayment 2238 ≤ upperValue ((point split endpoint 4096 2238+point split endpoint 4096 2239)/2)
    have hp : upperPayment 2238 = (249774255329:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2238+point split endpoint 4096 2239)/2 = (632449827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632449827:ℝ)/168755200)*ClassicalSixthBranch.v ((632449827:ℝ)/168755200)/ClassicalSixthBranch.r = (109799265854937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2238
  · change upperPayment 2239 ≤ upperValue ((point split endpoint 4096 2239+point split endpoint 4096 2240)/2)
    have hp : upperPayment 2239 = (249669319974:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2239+point split endpoint 4096 2240)/2 = (632474977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632474977:ℝ)/168755200)*ClassicalSixthBranch.v ((632474977:ℝ)/168755200)/ClassicalSixthBranch.r = (109777780435281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2239
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_139
