import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints143
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_143 (j : Fin 16) : upperPayment (16*143+j.val) ≤
    upperValue ((point split endpoint 4096 (16*143+j.val)+point split endpoint 4096 (16*143+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2288 ≤ upperValue ((point split endpoint 4096 2288+point split endpoint 4096 2289)/2)
    have hp : upperPayment 2288 = (244493664435:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2288+point split endpoint 4096 2289)/2 = (633707327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633707327:ℝ)/168755200)*ClassicalSixthBranch.v ((633707327:ℝ)/168755200)/ClassicalSixthBranch.r = (108727474360337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2288
  · change upperPayment 2289 ≤ upperValue ((point split endpoint 4096 2289+point split endpoint 4096 2290)/2)
    have hp : upperPayment 2289 = (244387346099:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2289+point split endpoint 4096 2290)/2 = (633732477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633732477:ℝ)/168755200)*ClassicalSixthBranch.v ((633732477:ℝ)/168755200)/ClassicalSixthBranch.r = (108706090144281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2289
  · change upperPayment 2290 ≤ upperValue ((point split endpoint 4096 2290+point split endpoint 4096 2291)/2)
    have hp : upperPayment 2290 = (244280999955:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2290+point split endpoint 4096 2291)/2 = (633757627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633757627:ℝ)/168755200)*ClassicalSixthBranch.v ((633757627:ℝ)/168755200)/ClassicalSixthBranch.r = (108684707952297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2290
  · change upperPayment 2291 ≤ upperValue ((point split endpoint 4096 2291+point split endpoint 4096 2292)/2)
    have hp : upperPayment 2291 = (244174625999:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2291+point split endpoint 4096 2292)/2 = (633782777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633782777:ℝ)/168755200)*ClassicalSixthBranch.v ((633782777:ℝ)/168755200)/ClassicalSixthBranch.r = (108663327784385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2291
  · change upperPayment 2292 ≤ upperValue ((point split endpoint 4096 2292+point split endpoint 4096 2293)/2)
    have hp : upperPayment 2292 = (244068224224:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2292+point split endpoint 4096 2293)/2 = (633807927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633807927:ℝ)/168755200)*ClassicalSixthBranch.v ((633807927:ℝ)/168755200)/ClassicalSixthBranch.r = (108641949640545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2292
  · change upperPayment 2293 ≤ upperValue ((point split endpoint 4096 2293+point split endpoint 4096 2294)/2)
    have hp : upperPayment 2293 = (243961794625:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2293+point split endpoint 4096 2294)/2 = (633833077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633833077:ℝ)/168755200)*ClassicalSixthBranch.v ((633833077:ℝ)/168755200)/ClassicalSixthBranch.r = (1054568674959:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2293
  · change upperPayment 2294 ≤ upperValue ((point split endpoint 4096 2294+point split endpoint 4096 2295)/2)
    have hp : upperPayment 2294 = (243855337196:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2294+point split endpoint 4096 2295)/2 = (633858227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633858227:ℝ)/168755200)*ClassicalSixthBranch.v ((633858227:ℝ)/168755200)/ClassicalSixthBranch.r = (108599199425081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2294
  · change upperPayment 2295 ≤ upperValue ((point split endpoint 4096 2295+point split endpoint 4096 2296)/2)
    have hp : upperPayment 2295 = (243748851931:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2295+point split endpoint 4096 2296)/2 = (633883377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633883377:ℝ)/168755200)*ClassicalSixthBranch.v ((633883377:ℝ)/168755200)/ClassicalSixthBranch.r = (108577827353457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2295
  · change upperPayment 2296 ≤ upperValue ((point split endpoint 4096 2296+point split endpoint 4096 2297)/2)
    have hp : upperPayment 2296 = (243642338824:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2296+point split endpoint 4096 2297)/2 = (633908527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633908527:ℝ)/168755200)*ClassicalSixthBranch.v ((633908527:ℝ)/168755200)/ClassicalSixthBranch.r = (108556457305905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2296
  · change upperPayment 2297 ≤ upperValue ((point split endpoint 4096 2297+point split endpoint 4096 2298)/2)
    have hp : upperPayment 2297 = (243535797869:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2297+point split endpoint 4096 2298)/2 = (633933677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633933677:ℝ)/168755200)*ClassicalSixthBranch.v ((633933677:ℝ)/168755200)/ClassicalSixthBranch.r = (108535089282425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2297
  · change upperPayment 2298 ≤ upperValue ((point split endpoint 4096 2298+point split endpoint 4096 2299)/2)
    have hp : upperPayment 2298 = (243429229061:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2298+point split endpoint 4096 2299)/2 = (633958827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633958827:ℝ)/168755200)*ClassicalSixthBranch.v ((633958827:ℝ)/168755200)/ClassicalSixthBranch.r = (108513723283017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2298
  · change upperPayment 2299 ≤ upperValue ((point split endpoint 4096 2299+point split endpoint 4096 2300)/2)
    have hp : upperPayment 2299 = (243322632394:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2299+point split endpoint 4096 2300)/2 = (633983977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633983977:ℝ)/168755200)*ClassicalSixthBranch.v ((633983977:ℝ)/168755200)/ClassicalSixthBranch.r = (108492359307681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2299
  · change upperPayment 2300 ≤ upperValue ((point split endpoint 4096 2300+point split endpoint 4096 2301)/2)
    have hp : upperPayment 2300 = (243216007861:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2300+point split endpoint 4096 2301)/2 = (634009127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634009127:ℝ)/168755200)*ClassicalSixthBranch.v ((634009127:ℝ)/168755200)/ClassicalSixthBranch.r = (108470997356417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2300
  · change upperPayment 2301 ≤ upperValue ((point split endpoint 4096 2301+point split endpoint 4096 2302)/2)
    have hp : upperPayment 2301 = (243109355458:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2301+point split endpoint 4096 2302)/2 = (634034277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634034277:ℝ)/168755200)*ClassicalSixthBranch.v ((634034277:ℝ)/168755200)/ClassicalSixthBranch.r = (108449637429225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2301
  · change upperPayment 2302 ≤ upperValue ((point split endpoint 4096 2302+point split endpoint 4096 2303)/2)
    have hp : upperPayment 2302 = (243002675177:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2302+point split endpoint 4096 2303)/2 = (634059427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634059427:ℝ)/168755200)*ClassicalSixthBranch.v ((634059427:ℝ)/168755200)/ClassicalSixthBranch.r = (108428279526105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2302
  · change upperPayment 2303 ≤ upperValue ((point split endpoint 4096 2303+point split endpoint 4096 2304)/2)
    have hp : upperPayment 2303 = (242895967015:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2303+point split endpoint 4096 2304)/2 = (634084577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634084577:ℝ)/168755200)*ClassicalSixthBranch.v ((634084577:ℝ)/168755200)/ClassicalSixthBranch.r = (108406923647057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2303
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_143
