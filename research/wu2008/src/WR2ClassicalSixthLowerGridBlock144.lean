import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints144
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_144 (j : Fin 16) : lowerPayment (16*144+j.val) ≤
    lowerValue ((point 2 split 4096 (16*144+j.val)+point 2 split 4096 (16*144+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2304 ≤ lowerValue ((point 2 split 4096 2304+point 2 split 4096 2305)/2)
    have hp : lowerPayment 2304 = (260005336050:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2304+point 2 split 4096 2305)/2 = (471775179:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471775179:ℝ)/168755200)/ClassicalSixthBranch.v ((471775179:ℝ)/168755200) = (635845814971:ℝ)/309944281752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2304
  · change lowerPayment 2305 ≤ lowerValue ((point 2 split 4096 2305+point 2 split 4096 2306)/2)
    have hp : lowerPayment 2305 = (260094058097:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2305+point 2 split 4096 2306)/2 = (471833441:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471833441:ℝ)/168755200)/ClassicalSixthBranch.v ((471833441:ℝ)/168755200) = (635768501297:ℝ)/309896273864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2305
  · change lowerPayment 2306 ≤ lowerValue ((point 2 split 4096 2306+point 2 split 4096 2307)/2)
    have hp : lowerPayment 2306 = (260182774803:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2306+point 2 split 4096 2307)/2 = (471891703:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471891703:ℝ)/168755200)/ClassicalSixthBranch.v ((471891703:ℝ)/168755200) = (635691187623:ℝ)/309848265976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2306
  · change lowerPayment 2307 ≤ lowerValue ((point 2 split 4096 2307+point 2 split 4096 2308)/2)
    have hp : lowerPayment 2307 = (260271486182:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2307+point 2 split 4096 2308)/2 = (94389993:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94389993:ℝ)/33751040)/ClassicalSixthBranch.v ((94389993:ℝ)/33751040) = (635613873949:ℝ)/309800258088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2307
  · change lowerPayment 2308 ≤ lowerValue ((point 2 split 4096 2308+point 2 split 4096 2309)/2)
    have hp : lowerPayment 2308 = (260360192251:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2308+point 2 split 4096 2309)/2 = (472008227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472008227:ℝ)/168755200)/ClassicalSixthBranch.v ((472008227:ℝ)/168755200) = (25421462411:ℝ)/12390090008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2308
  · change lowerPayment 2309 ≤ lowerValue ((point 2 split 4096 2309+point 2 split 4096 2310)/2)
    have hp : lowerPayment 2309 = (260448893023:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2309+point 2 split 4096 2310)/2 = (472066489:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472066489:ℝ)/168755200)/ClassicalSixthBranch.v ((472066489:ℝ)/168755200) = (635459246601:ℝ)/309704242312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2309
  · change lowerPayment 2310 ≤ lowerValue ((point 2 split 4096 2310+point 2 split 4096 2311)/2)
    have hp : lowerPayment 2310 = (260537588515:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2310+point 2 split 4096 2311)/2 = (472124751:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472124751:ℝ)/168755200)/ClassicalSixthBranch.v ((472124751:ℝ)/168755200) = (635381932927:ℝ)/309656234424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2310
  · change lowerPayment 2311 ≤ lowerValue ((point 2 split 4096 2311+point 2 split 4096 2312)/2)
    have hp : lowerPayment 2311 = (260626278742:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2311+point 2 split 4096 2312)/2 = (472183013:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472183013:ℝ)/168755200)/ClassicalSixthBranch.v ((472183013:ℝ)/168755200) = (635304619253:ℝ)/309608226536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2311
  · change lowerPayment 2312 ≤ lowerValue ((point 2 split 4096 2312+point 2 split 4096 2313)/2)
    have hp : lowerPayment 2312 = (260714963718:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2312+point 2 split 4096 2313)/2 = (18889651:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18889651:ℝ)/6750208)/ClassicalSixthBranch.v ((18889651:ℝ)/6750208) = (635227305579:ℝ)/309560218648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2312
  · change lowerPayment 2313 ≤ lowerValue ((point 2 split 4096 2313+point 2 split 4096 2314)/2)
    have hp : lowerPayment 2313 = (260803643458:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2313+point 2 split 4096 2314)/2 = (472299537:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472299537:ℝ)/168755200)/ClassicalSixthBranch.v ((472299537:ℝ)/168755200) = (127029998381:ℝ)/61902442152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2313
  · change lowerPayment 2314 ≤ lowerValue ((point 2 split 4096 2314+point 2 split 4096 2315)/2)
    have hp : lowerPayment 2314 = (260892317978:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2314+point 2 split 4096 2315)/2 = (472357799:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472357799:ℝ)/168755200)/ClassicalSixthBranch.v ((472357799:ℝ)/168755200) = (635072678231:ℝ)/309464202872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2314
  · change lowerPayment 2315 ≤ lowerValue ((point 2 split 4096 2315+point 2 split 4096 2316)/2)
    have hp : lowerPayment 2315 = (260980987293:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2315+point 2 split 4096 2316)/2 = (472416061:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472416061:ℝ)/168755200)/ClassicalSixthBranch.v ((472416061:ℝ)/168755200) = (634995364557:ℝ)/309416194984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2315
  · change lowerPayment 2316 ≤ lowerValue ((point 2 split 4096 2316+point 2 split 4096 2317)/2)
    have hp : lowerPayment 2316 = (261069651419:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2316+point 2 split 4096 2317)/2 = (472474323:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472474323:ℝ)/168755200)/ClassicalSixthBranch.v ((472474323:ℝ)/168755200) = (634918050883:ℝ)/309368187096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2316
  · change lowerPayment 2317 ≤ lowerValue ((point 2 split 4096 2317+point 2 split 4096 2318)/2)
    have hp : lowerPayment 2317 = (261158310369:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2317+point 2 split 4096 2318)/2 = (917539:ℝ)/327680 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((917539:ℝ)/327680)/ClassicalSixthBranch.v ((917539:ℝ)/327680) = (6163502303:ℝ)/3003108536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2317
  · change lowerPayment 2318 ≤ lowerValue ((point 2 split 4096 2318+point 2 split 4096 2319)/2)
    have hp : lowerPayment 2318 = (261246964159:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2318+point 2 split 4096 2319)/2 = (472590847:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472590847:ℝ)/168755200)/ClassicalSixthBranch.v ((472590847:ℝ)/168755200) = (126952684707:ℝ)/61854434264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2318
  · change lowerPayment 2319 ≤ lowerValue ((point 2 split 4096 2319+point 2 split 4096 2320)/2)
    have hp : lowerPayment 2319 = (261335612805:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2319+point 2 split 4096 2320)/2 = (472649109:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472649109:ℝ)/168755200)/ClassicalSixthBranch.v ((472649109:ℝ)/168755200) = (634686109861:ℝ)/309224163432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2319
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_144
