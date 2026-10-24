import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints153
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_153 (j : Fin 16) : upperPayment (16*153+j.val) ≤
    upperValue ((point split endpoint 4096 (16*153+j.val)+point split endpoint 4096 (16*153+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2448 ≤ upperValue ((point split endpoint 4096 2448+point split endpoint 4096 2449)/2)
    have hp : upperPayment 2448 = (227125069719:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2448+point split endpoint 4096 2449)/2 = (637731327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637731327:ℝ)/168755200)*ClassicalSixthBranch.v ((637731327:ℝ)/168755200)/ClassicalSixthBranch.r = (105331745987217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2448
  · change upperPayment 2449 ≤ upperValue ((point split endpoint 4096 2449+point split endpoint 4096 2450)/2)
    have hp : upperPayment 2449 = (227014226733:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2449+point split endpoint 4096 2450)/2 = (637756477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637756477:ℝ)/168755200)*ClassicalSixthBranch.v ((637756477:ℝ)/168755200)/ClassicalSixthBranch.r = (105310685622681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2449
  · change upperPayment 2450 ≤ upperValue ((point split endpoint 4096 2450+point split endpoint 4096 2451)/2)
    have hp : upperPayment 2450 = (226903354980:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2450+point split endpoint 4096 2451)/2 = (637781627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637781627:ℝ)/168755200)*ClassicalSixthBranch.v ((637781627:ℝ)/168755200)/ClassicalSixthBranch.r = (105289627282217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2450
  · change upperPayment 2451 ≤ upperValue ((point split endpoint 4096 2451+point split endpoint 4096 2452)/2)
    have hp : upperPayment 2451 = (226792454453:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2451+point split endpoint 4096 2452)/2 = (637806777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637806777:ℝ)/168755200)*ClassicalSixthBranch.v ((637806777:ℝ)/168755200)/ClassicalSixthBranch.r = (105268570965825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2451
  · change upperPayment 2452 ≤ upperValue ((point split endpoint 4096 2452+point split endpoint 4096 2453)/2)
    have hp : upperPayment 2452 = (226681525145:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2452+point split endpoint 4096 2453)/2 = (637831927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637831927:ℝ)/168755200)*ClassicalSixthBranch.v ((637831927:ℝ)/168755200)/ClassicalSixthBranch.r = (105247516673505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2452
  · change upperPayment 2453 ≤ upperValue ((point split endpoint 4096 2453+point split endpoint 4096 2454)/2)
    have hp : upperPayment 2453 = (226570567052:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2453+point split endpoint 4096 2454)/2 = (637857077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637857077:ℝ)/168755200)*ClassicalSixthBranch.v ((637857077:ℝ)/168755200)/ClassicalSixthBranch.r = (105226464405257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2453
  · change upperPayment 2454 ≤ upperValue ((point split endpoint 4096 2454+point split endpoint 4096 2455)/2)
    have hp : upperPayment 2454 = (226459580167:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2454+point split endpoint 4096 2455)/2 = (637882227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637882227:ℝ)/168755200)*ClassicalSixthBranch.v ((637882227:ℝ)/168755200)/ClassicalSixthBranch.r = (105205414161081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2454
  · change upperPayment 2455 ≤ upperValue ((point split endpoint 4096 2455+point split endpoint 4096 2456)/2)
    have hp : upperPayment 2455 = (226348564483:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2455+point split endpoint 4096 2456)/2 = (637907377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637907377:ℝ)/168755200)*ClassicalSixthBranch.v ((637907377:ℝ)/168755200)/ClassicalSixthBranch.r = (105184365940977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2455
  · change upperPayment 2456 ≤ upperValue ((point split endpoint 4096 2456+point split endpoint 4096 2457)/2)
    have hp : upperPayment 2456 = (226237519994:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2456+point split endpoint 4096 2457)/2 = (637932527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637932527:ℝ)/168755200)*ClassicalSixthBranch.v ((637932527:ℝ)/168755200)/ClassicalSixthBranch.r = (105163319744945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2456
  · change upperPayment 2457 ≤ upperValue ((point split endpoint 4096 2457+point split endpoint 4096 2458)/2)
    have hp : upperPayment 2457 = (226126446694:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2457+point split endpoint 4096 2458)/2 = (637957677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637957677:ℝ)/168755200)*ClassicalSixthBranch.v ((637957677:ℝ)/168755200)/ClassicalSixthBranch.r = (105142275572985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2457
  · change upperPayment 2458 ≤ upperValue ((point split endpoint 4096 2458+point split endpoint 4096 2459)/2)
    have hp : upperPayment 2458 = (226015344577:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2458+point split endpoint 4096 2459)/2 = (637982827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((637982827:ℝ)/168755200)*ClassicalSixthBranch.v ((637982827:ℝ)/168755200)/ClassicalSixthBranch.r = (105121233425097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2458
  · change upperPayment 2459 ≤ upperValue ((point split endpoint 4096 2459+point split endpoint 4096 2460)/2)
    have hp : upperPayment 2459 = (225904213637:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2459+point split endpoint 4096 2460)/2 = (638007977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638007977:ℝ)/168755200)*ClassicalSixthBranch.v ((638007977:ℝ)/168755200)/ClassicalSixthBranch.r = (105100193301281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2459
  · change upperPayment 2460 ≤ upperValue ((point split endpoint 4096 2460+point split endpoint 4096 2461)/2)
    have hp : upperPayment 2460 = (225793053867:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2460+point split endpoint 4096 2461)/2 = (638033127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638033127:ℝ)/168755200)*ClassicalSixthBranch.v ((638033127:ℝ)/168755200)/ClassicalSixthBranch.r = (105079155201537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2460
  · change upperPayment 2461 ≤ upperValue ((point split endpoint 4096 2461+point split endpoint 4096 2462)/2)
    have hp : upperPayment 2461 = (225681865261:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2461+point split endpoint 4096 2462)/2 = (638058277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638058277:ℝ)/168755200)*ClassicalSixthBranch.v ((638058277:ℝ)/168755200)/ClassicalSixthBranch.r = (105058119125865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2461
  · change upperPayment 2462 ≤ upperValue ((point split endpoint 4096 2462+point split endpoint 4096 2463)/2)
    have hp : upperPayment 2462 = (225570647813:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2462+point split endpoint 4096 2463)/2 = (638083427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638083427:ℝ)/168755200)*ClassicalSixthBranch.v ((638083427:ℝ)/168755200)/ClassicalSixthBranch.r = (105037085074265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2462
  · change upperPayment 2463 ≤ upperValue ((point split endpoint 4096 2463+point split endpoint 4096 2464)/2)
    have hp : upperPayment 2463 = (225459401516:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2463+point split endpoint 4096 2464)/2 = (638108577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((638108577:ℝ)/168755200)*ClassicalSixthBranch.v ((638108577:ℝ)/168755200)/ClassicalSixthBranch.r = (105016053046737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2463
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_153
