import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints142
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_142 (j : Fin 16) : upperPayment (16*142+j.val) ≤
    upperValue ((point split endpoint 4096 (16*142+j.val)+point split endpoint 4096 (16*142+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2272 ≤ upperValue ((point split endpoint 4096 2272+point split endpoint 4096 2273)/2)
    have hp : upperPayment 2272 = (246190980824:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2272+point split endpoint 4096 2273)/2 = (633304927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633304927:ℝ)/168755200)*ClassicalSixthBranch.v ((633304927:ℝ)/168755200)/ClassicalSixthBranch.r = (109069897091025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2272
  · change upperPayment 2273 ≤ upperValue ((point split endpoint 4096 2273+point split endpoint 4096 2274)/2)
    have hp : upperPayment 2273 = (246085106608:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2273+point split endpoint 4096 2274)/2 = (633330077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633330077:ℝ)/168755200)*ClassicalSixthBranch.v ((633330077:ℝ)/168755200)/ClassicalSixthBranch.r = (109048480489817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2273
  · change upperPayment 2274 ≤ upperValue ((point split endpoint 4096 2274+point split endpoint 4096 2275)/2)
    have hp : upperPayment 2274 = (245979204678:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2274+point split endpoint 4096 2275)/2 = (633355227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633355227:ℝ)/168755200)*ClassicalSixthBranch.v ((633355227:ℝ)/168755200)/ClassicalSixthBranch.r = (109027065912681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2274
  · change upperPayment 2275 ≤ upperValue ((point split endpoint 4096 2275+point split endpoint 4096 2276)/2)
    have hp : upperPayment 2275 = (245873275028:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2275+point split endpoint 4096 2276)/2 = (633380377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633380377:ℝ)/168755200)*ClassicalSixthBranch.v ((633380377:ℝ)/168755200)/ClassicalSixthBranch.r = (109005653359617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2275
  · change upperPayment 2276 ≤ upperValue ((point split endpoint 4096 2276+point split endpoint 4096 2277)/2)
    have hp : upperPayment 2276 = (245767317653:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2276+point split endpoint 4096 2277)/2 = (633405527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633405527:ℝ)/168755200)*ClassicalSixthBranch.v ((633405527:ℝ)/168755200)/ClassicalSixthBranch.r = (108984242830625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2276
  · change upperPayment 2277 ≤ upperValue ((point split endpoint 4096 2277+point split endpoint 4096 2278)/2)
    have hp : upperPayment 2277 = (245661332546:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2277+point split endpoint 4096 2278)/2 = (633430677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633430677:ℝ)/168755200)*ClassicalSixthBranch.v ((633430677:ℝ)/168755200)/ClassicalSixthBranch.r = (108962834325705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2277
  · change upperPayment 2278 ≤ upperValue ((point split endpoint 4096 2278+point split endpoint 4096 2279)/2)
    have hp : upperPayment 2278 = (245555319702:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2278+point split endpoint 4096 2279)/2 = (633455827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633455827:ℝ)/168755200)*ClassicalSixthBranch.v ((633455827:ℝ)/168755200)/ClassicalSixthBranch.r = (108941427844857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2278
  · change upperPayment 2279 ≤ upperValue ((point split endpoint 4096 2279+point split endpoint 4096 2280)/2)
    have hp : upperPayment 2279 = (245449279115:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2279+point split endpoint 4096 2280)/2 = (633480977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633480977:ℝ)/168755200)*ClassicalSixthBranch.v ((633480977:ℝ)/168755200)/ClassicalSixthBranch.r = (108920023388081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2279
  · change upperPayment 2280 ≤ upperValue ((point split endpoint 4096 2280+point split endpoint 4096 2281)/2)
    have hp : upperPayment 2280 = (245343210779:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2280+point split endpoint 4096 2281)/2 = (633506127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633506127:ℝ)/168755200)*ClassicalSixthBranch.v ((633506127:ℝ)/168755200)/ClassicalSixthBranch.r = (108898620955377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2280
  · change upperPayment 2281 ≤ upperValue ((point split endpoint 4096 2281+point split endpoint 4096 2282)/2)
    have hp : upperPayment 2281 = (245237114688:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2281+point split endpoint 4096 2282)/2 = (633531277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633531277:ℝ)/168755200)*ClassicalSixthBranch.v ((633531277:ℝ)/168755200)/ClassicalSixthBranch.r = (108877220546745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2281
  · change upperPayment 2282 ≤ upperValue ((point split endpoint 4096 2282+point split endpoint 4096 2283)/2)
    have hp : upperPayment 2282 = (245130990837:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2282+point split endpoint 4096 2283)/2 = (633556427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633556427:ℝ)/168755200)*ClassicalSixthBranch.v ((633556427:ℝ)/168755200)/ClassicalSixthBranch.r = (108855822162185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2282
  · change upperPayment 2283 ≤ upperValue ((point split endpoint 4096 2283+point split endpoint 4096 2284)/2)
    have hp : upperPayment 2283 = (245024839219:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2283+point split endpoint 4096 2284)/2 = (633581577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633581577:ℝ)/168755200)*ClassicalSixthBranch.v ((633581577:ℝ)/168755200)/ClassicalSixthBranch.r = (108834425801697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2283
  · change upperPayment 2284 ≤ upperValue ((point split endpoint 4096 2284+point split endpoint 4096 2285)/2)
    have hp : upperPayment 2284 = (244918659830:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2284+point split endpoint 4096 2285)/2 = (633606727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633606727:ℝ)/168755200)*ClassicalSixthBranch.v ((633606727:ℝ)/168755200)/ClassicalSixthBranch.r = (108813031465281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2284
  · change upperPayment 2285 ≤ upperValue ((point split endpoint 4096 2285+point split endpoint 4096 2286)/2)
    have hp : upperPayment 2285 = (244812452662:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2285+point split endpoint 4096 2286)/2 = (633631877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633631877:ℝ)/168755200)*ClassicalSixthBranch.v ((633631877:ℝ)/168755200)/ClassicalSixthBranch.r = (108791639152937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2285
  · change upperPayment 2286 ≤ upperValue ((point split endpoint 4096 2286+point split endpoint 4096 2287)/2)
    have hp : upperPayment 2286 = (244706217711:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2286+point split endpoint 4096 2287)/2 = (633657027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633657027:ℝ)/168755200)*ClassicalSixthBranch.v ((633657027:ℝ)/168755200)/ClassicalSixthBranch.r = (108770248864665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2286
  · change upperPayment 2287 ≤ upperValue ((point split endpoint 4096 2287+point split endpoint 4096 2288)/2)
    have hp : upperPayment 2287 = (244599954971:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2287+point split endpoint 4096 2288)/2 = (633682177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((633682177:ℝ)/168755200)*ClassicalSixthBranch.v ((633682177:ℝ)/168755200)/ClassicalSixthBranch.r = (108748860600465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2287
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_142
