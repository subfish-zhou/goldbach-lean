import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints140
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_140 (j : Fin 16) : upperPayment (16*140+j.val) ≤
    upperValue ((point split endpoint 4096 (16*140+j.val)+point split endpoint 4096 (16*140+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2240 ≤ upperValue ((point split endpoint 4096 2240+point split endpoint 4096 2241)/2)
    have hp : upperPayment 2240 = (249564357099:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2240+point split endpoint 4096 2241)/2 = (632500127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632500127:ℝ)/168755200)*ClassicalSixthBranch.v ((632500127:ℝ)/168755200)/ClassicalSixthBranch.r = (109756297039697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2240
  · change upperPayment 2241 ≤ upperValue ((point split endpoint 4096 2241+point split endpoint 4096 2242)/2)
    have hp : upperPayment 2241 = (249459366700:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2241+point split endpoint 4096 2242)/2 = (632525277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632525277:ℝ)/168755200)*ClassicalSixthBranch.v ((632525277:ℝ)/168755200)/ClassicalSixthBranch.r = (109734815668185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2241
  · change upperPayment 2242 ≤ upperValue ((point split endpoint 4096 2242+point split endpoint 4096 2243)/2)
    have hp : upperPayment 2242 = (249354348771:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2242+point split endpoint 4096 2243)/2 = (632550427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632550427:ℝ)/168755200)*ClassicalSixthBranch.v ((632550427:ℝ)/168755200)/ClassicalSixthBranch.r = (109713336320745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2242
  · change upperPayment 2243 ≤ upperValue ((point split endpoint 4096 2243+point split endpoint 4096 2244)/2)
    have hp : upperPayment 2243 = (249249303305:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2243+point split endpoint 4096 2244)/2 = (632575577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632575577:ℝ)/168755200)*ClassicalSixthBranch.v ((632575577:ℝ)/168755200)/ClassicalSixthBranch.r = (109691858997377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2243
  · change upperPayment 2244 ≤ upperValue ((point split endpoint 4096 2244+point split endpoint 4096 2245)/2)
    have hp : upperPayment 2244 = (249144230297:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2244+point split endpoint 4096 2245)/2 = (632600727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632600727:ℝ)/168755200)*ClassicalSixthBranch.v ((632600727:ℝ)/168755200)/ClassicalSixthBranch.r = (109670383698081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2244
  · change upperPayment 2245 ≤ upperValue ((point split endpoint 4096 2245+point split endpoint 4096 2246)/2)
    have hp : upperPayment 2245 = (249039129741:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2245+point split endpoint 4096 2246)/2 = (632625877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632625877:ℝ)/168755200)*ClassicalSixthBranch.v ((632625877:ℝ)/168755200)/ClassicalSixthBranch.r = (109648910422857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2245
  · change upperPayment 2246 ≤ upperValue ((point split endpoint 4096 2246+point split endpoint 4096 2247)/2)
    have hp : upperPayment 2246 = (248934001633:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2246+point split endpoint 4096 2247)/2 = (632651027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632651027:ℝ)/168755200)*ClassicalSixthBranch.v ((632651027:ℝ)/168755200)/ClassicalSixthBranch.r = (109627439171705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2246
  · change upperPayment 2247 ≤ upperValue ((point split endpoint 4096 2247+point split endpoint 4096 2248)/2)
    have hp : upperPayment 2247 = (248828845965:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2247+point split endpoint 4096 2248)/2 = (632676177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632676177:ℝ)/168755200)*ClassicalSixthBranch.v ((632676177:ℝ)/168755200)/ClassicalSixthBranch.r = (109605969944625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2247
  · change upperPayment 2248 ≤ upperValue ((point split endpoint 4096 2248+point split endpoint 4096 2249)/2)
    have hp : upperPayment 2248 = (248723662732:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2248+point split endpoint 4096 2249)/2 = (632701327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632701327:ℝ)/168755200)*ClassicalSixthBranch.v ((632701327:ℝ)/168755200)/ClassicalSixthBranch.r = (109584502741617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2248
  · change upperPayment 2249 ≤ upperValue ((point split endpoint 4096 2249+point split endpoint 4096 2250)/2)
    have hp : upperPayment 2249 = (248618451929:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2249+point split endpoint 4096 2250)/2 = (632726477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632726477:ℝ)/168755200)*ClassicalSixthBranch.v ((632726477:ℝ)/168755200)/ClassicalSixthBranch.r = (109563037562681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2249
  · change upperPayment 2250 ≤ upperValue ((point split endpoint 4096 2250+point split endpoint 4096 2251)/2)
    have hp : upperPayment 2250 = (248513213550:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2250+point split endpoint 4096 2251)/2 = (632751627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632751627:ℝ)/168755200)*ClassicalSixthBranch.v ((632751627:ℝ)/168755200)/ClassicalSixthBranch.r = (109541574407817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2250
  · change upperPayment 2251 ≤ upperValue ((point split endpoint 4096 2251+point split endpoint 4096 2252)/2)
    have hp : upperPayment 2251 = (248407947589:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2251+point split endpoint 4096 2252)/2 = (632776777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632776777:ℝ)/168755200)*ClassicalSixthBranch.v ((632776777:ℝ)/168755200)/ClassicalSixthBranch.r = (109520113277025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2251
  · change upperPayment 2252 ≤ upperValue ((point split endpoint 4096 2252+point split endpoint 4096 2253)/2)
    have hp : upperPayment 2252 = (248302654040:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2252+point split endpoint 4096 2253)/2 = (632801927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632801927:ℝ)/168755200)*ClassicalSixthBranch.v ((632801927:ℝ)/168755200)/ClassicalSixthBranch.r = (109498654170305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2252
  · change upperPayment 2253 ≤ upperValue ((point split endpoint 4096 2253+point split endpoint 4096 2254)/2)
    have hp : upperPayment 2253 = (248197332898:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2253+point split endpoint 4096 2254)/2 = (632827077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632827077:ℝ)/168755200)*ClassicalSixthBranch.v ((632827077:ℝ)/168755200)/ClassicalSixthBranch.r = (109477197087657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2253
  · change upperPayment 2254 ≤ upperValue ((point split endpoint 4096 2254+point split endpoint 4096 2255)/2)
    have hp : upperPayment 2254 = (248091984156:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2254+point split endpoint 4096 2255)/2 = (632852227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632852227:ℝ)/168755200)*ClassicalSixthBranch.v ((632852227:ℝ)/168755200)/ClassicalSixthBranch.r = (109455742029081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2254
  · change upperPayment 2255 ≤ upperValue ((point split endpoint 4096 2255+point split endpoint 4096 2256)/2)
    have hp : upperPayment 2255 = (247986607810:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2255+point split endpoint 4096 2256)/2 = (632877377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((632877377:ℝ)/168755200)*ClassicalSixthBranch.v ((632877377:ℝ)/168755200)/ClassicalSixthBranch.r = (109434288994577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2255
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_140
