import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints144
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_144 (j : Fin 16) : upperPayment (16*144+j.val) ≤
    upperValue ((point split endpoint 4096 (16*144+j.val)+point split endpoint 4096 (16*144+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2304 ≤ upperValue ((point split endpoint 4096 2304+point split endpoint 4096 2305)/2)
    have hp : upperPayment 2304 = (242789230963:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2304+point split endpoint 4096 2305)/2 = (634109727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634109727:ℝ)/168755200)*ClassicalSixthBranch.v ((634109727:ℝ)/168755200)/ClassicalSixthBranch.r = (108385569792081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2304
  · change upperPayment 2305 ≤ upperValue ((point split endpoint 4096 2305+point split endpoint 4096 2306)/2)
    have hp : upperPayment 2305 = (242682467017:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2305+point split endpoint 4096 2306)/2 = (634134877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634134877:ℝ)/168755200)*ClassicalSixthBranch.v ((634134877:ℝ)/168755200)/ClassicalSixthBranch.r = (108364217961177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2305
  · change upperPayment 2306 ≤ upperValue ((point split endpoint 4096 2306+point split endpoint 4096 2307)/2)
    have hp : upperPayment 2306 = (242575675172:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2306+point split endpoint 4096 2307)/2 = (634160027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634160027:ℝ)/168755200)*ClassicalSixthBranch.v ((634160027:ℝ)/168755200)/ClassicalSixthBranch.r = (108342868154345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2306
  · change upperPayment 2307 ≤ upperValue ((point split endpoint 4096 2307+point split endpoint 4096 2308)/2)
    have hp : upperPayment 2307 = (242468855420:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2307+point split endpoint 4096 2308)/2 = (634185177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634185177:ℝ)/168755200)*ClassicalSixthBranch.v ((634185177:ℝ)/168755200)/ClassicalSixthBranch.r = (108321520371585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2307
  · change upperPayment 2308 ≤ upperValue ((point split endpoint 4096 2308+point split endpoint 4096 2309)/2)
    have hp : upperPayment 2308 = (242362007756:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2308+point split endpoint 4096 2309)/2 = (634210327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634210327:ℝ)/168755200)*ClassicalSixthBranch.v ((634210327:ℝ)/168755200)/ClassicalSixthBranch.r = (108300174612897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2308
  · change upperPayment 2309 ≤ upperValue ((point split endpoint 4096 2309+point split endpoint 4096 2310)/2)
    have hp : upperPayment 2309 = (242255132174:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2309+point split endpoint 4096 2310)/2 = (634235477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634235477:ℝ)/168755200)*ClassicalSixthBranch.v ((634235477:ℝ)/168755200)/ClassicalSixthBranch.r = (108278830878281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2309
  · change upperPayment 2310 ≤ upperValue ((point split endpoint 4096 2310+point split endpoint 4096 2311)/2)
    have hp : upperPayment 2310 = (242148228669:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2310+point split endpoint 4096 2311)/2 = (634260627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634260627:ℝ)/168755200)*ClassicalSixthBranch.v ((634260627:ℝ)/168755200)/ClassicalSixthBranch.r = (108257489167737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2310
  · change upperPayment 2311 ≤ upperValue ((point split endpoint 4096 2311+point split endpoint 4096 2312)/2)
    have hp : upperPayment 2311 = (242041297234:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2311+point split endpoint 4096 2312)/2 = (634285777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634285777:ℝ)/168755200)*ClassicalSixthBranch.v ((634285777:ℝ)/168755200)/ClassicalSixthBranch.r = (108236149481265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2311
  · change upperPayment 2312 ≤ upperValue ((point split endpoint 4096 2312+point split endpoint 4096 2313)/2)
    have hp : upperPayment 2312 = (241934337864:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2312+point split endpoint 4096 2313)/2 = (634310927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634310927:ℝ)/168755200)*ClassicalSixthBranch.v ((634310927:ℝ)/168755200)/ClassicalSixthBranch.r = (108214811818865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2312
  · change upperPayment 2313 ≤ upperValue ((point split endpoint 4096 2313+point split endpoint 4096 2314)/2)
    have hp : upperPayment 2313 = (241827350553:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2313+point split endpoint 4096 2314)/2 = (634336077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634336077:ℝ)/168755200)*ClassicalSixthBranch.v ((634336077:ℝ)/168755200)/ClassicalSixthBranch.r = (108193476180537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2313
  · change upperPayment 2314 ≤ upperValue ((point split endpoint 4096 2314+point split endpoint 4096 2315)/2)
    have hp : upperPayment 2314 = (241720335295:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2314+point split endpoint 4096 2315)/2 = (634361227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634361227:ℝ)/168755200)*ClassicalSixthBranch.v ((634361227:ℝ)/168755200)/ClassicalSixthBranch.r = (108172142566281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2314
  · change upperPayment 2315 ≤ upperValue ((point split endpoint 4096 2315+point split endpoint 4096 2316)/2)
    have hp : upperPayment 2315 = (241613292084:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2315+point split endpoint 4096 2316)/2 = (634386377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634386377:ℝ)/168755200)*ClassicalSixthBranch.v ((634386377:ℝ)/168755200)/ClassicalSixthBranch.r = (108150810976097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2315
  · change upperPayment 2316 ≤ upperValue ((point split endpoint 4096 2316+point split endpoint 4096 2317)/2)
    have hp : upperPayment 2316 = (241506220914:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2316+point split endpoint 4096 2317)/2 = (634411527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634411527:ℝ)/168755200)*ClassicalSixthBranch.v ((634411527:ℝ)/168755200)/ClassicalSixthBranch.r = (108129481409985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2316
  · change upperPayment 2317 ≤ upperValue ((point split endpoint 4096 2317+point split endpoint 4096 2318)/2)
    have hp : upperPayment 2317 = (241399121779:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2317+point split endpoint 4096 2318)/2 = (634436677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634436677:ℝ)/168755200)*ClassicalSixthBranch.v ((634436677:ℝ)/168755200)/ClassicalSixthBranch.r = (108108153867945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2317
  · change upperPayment 2318 ≤ upperValue ((point split endpoint 4096 2318+point split endpoint 4096 2319)/2)
    have hp : upperPayment 2318 = (241291994674:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2318+point split endpoint 4096 2319)/2 = (634461827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634461827:ℝ)/168755200)*ClassicalSixthBranch.v ((634461827:ℝ)/168755200)/ClassicalSixthBranch.r = (108086828349977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2318
  · change upperPayment 2319 ≤ upperValue ((point split endpoint 4096 2319+point split endpoint 4096 2320)/2)
    have hp : upperPayment 2319 = (241184839592:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2319+point split endpoint 4096 2320)/2 = (634486977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634486977:ℝ)/168755200)*ClassicalSixthBranch.v ((634486977:ℝ)/168755200)/ClassicalSixthBranch.r = (108065504856081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2319
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_144
