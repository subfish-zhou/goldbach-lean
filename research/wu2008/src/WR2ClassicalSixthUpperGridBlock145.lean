import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints145
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_145 (j : Fin 16) : upperPayment (16*145+j.val) ≤
    upperValue ((point split endpoint 4096 (16*145+j.val)+point split endpoint 4096 (16*145+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2320 ≤ upperValue ((point split endpoint 4096 2320+point split endpoint 4096 2321)/2)
    have hp : upperPayment 2320 = (241077656528:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2320+point split endpoint 4096 2321)/2 = (634512127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634512127:ℝ)/168755200)*ClassicalSixthBranch.v ((634512127:ℝ)/168755200)/ClassicalSixthBranch.r = (108044183386257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2320
  · change upperPayment 2321 ≤ upperValue ((point split endpoint 4096 2321+point split endpoint 4096 2322)/2)
    have hp : upperPayment 2321 = (240970445476:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2321+point split endpoint 4096 2322)/2 = (634537277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634537277:ℝ)/168755200)*ClassicalSixthBranch.v ((634537277:ℝ)/168755200)/ClassicalSixthBranch.r = (108022863940505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2321
  · change upperPayment 2322 ≤ upperValue ((point split endpoint 4096 2322+point split endpoint 4096 2323)/2)
    have hp : upperPayment 2322 = (240863206430:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2322+point split endpoint 4096 2323)/2 = (634562427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634562427:ℝ)/168755200)*ClassicalSixthBranch.v ((634562427:ℝ)/168755200)/ClassicalSixthBranch.r = (108001546518825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2322
  · change upperPayment 2323 ≤ upperValue ((point split endpoint 4096 2323+point split endpoint 4096 2324)/2)
    have hp : upperPayment 2323 = (240755939383:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2323+point split endpoint 4096 2324)/2 = (634587577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634587577:ℝ)/168755200)*ClassicalSixthBranch.v ((634587577:ℝ)/168755200)/ClassicalSixthBranch.r = (107980231121217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2323
  · change upperPayment 2324 ≤ upperValue ((point split endpoint 4096 2324+point split endpoint 4096 2325)/2)
    have hp : upperPayment 2324 = (240648644331:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2324+point split endpoint 4096 2325)/2 = (634612727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634612727:ℝ)/168755200)*ClassicalSixthBranch.v ((634612727:ℝ)/168755200)/ClassicalSixthBranch.r = (107958917747681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2324
  · change upperPayment 2325 ≤ upperValue ((point split endpoint 4096 2325+point split endpoint 4096 2326)/2)
    have hp : upperPayment 2325 = (240541321267:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2325+point split endpoint 4096 2326)/2 = (634637877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634637877:ℝ)/168755200)*ClassicalSixthBranch.v ((634637877:ℝ)/168755200)/ClassicalSixthBranch.r = (107937606398217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2325
  · change upperPayment 2326 ≤ upperValue ((point split endpoint 4096 2326+point split endpoint 4096 2327)/2)
    have hp : upperPayment 2326 = (240433970186:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2326+point split endpoint 4096 2327)/2 = (634663027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634663027:ℝ)/168755200)*ClassicalSixthBranch.v ((634663027:ℝ)/168755200)/ClassicalSixthBranch.r = (107916297072825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2326
  · change upperPayment 2327 ≤ upperValue ((point split endpoint 4096 2327+point split endpoint 4096 2328)/2)
    have hp : upperPayment 2327 = (240326591080:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2327+point split endpoint 4096 2328)/2 = (634688177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634688177:ℝ)/168755200)*ClassicalSixthBranch.v ((634688177:ℝ)/168755200)/ClassicalSixthBranch.r = (107894989771505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2327
  · change upperPayment 2328 ≤ upperValue ((point split endpoint 4096 2328+point split endpoint 4096 2329)/2)
    have hp : upperPayment 2328 = (240219183946:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2328+point split endpoint 4096 2329)/2 = (634713327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634713327:ℝ)/168755200)*ClassicalSixthBranch.v ((634713327:ℝ)/168755200)/ClassicalSixthBranch.r = (107873684494257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2328
  · change upperPayment 2329 ≤ upperValue ((point split endpoint 4096 2329+point split endpoint 4096 2330)/2)
    have hp : upperPayment 2329 = (240111748776:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2329+point split endpoint 4096 2330)/2 = (634738477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634738477:ℝ)/168755200)*ClassicalSixthBranch.v ((634738477:ℝ)/168755200)/ClassicalSixthBranch.r = (107852381241081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2329
  · change upperPayment 2330 ≤ upperValue ((point split endpoint 4096 2330+point split endpoint 4096 2331)/2)
    have hp : upperPayment 2330 = (240004285564:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2330+point split endpoint 4096 2331)/2 = (634763627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634763627:ℝ)/168755200)*ClassicalSixthBranch.v ((634763627:ℝ)/168755200)/ClassicalSixthBranch.r = (107831080011977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2330
  · change upperPayment 2331 ≤ upperValue ((point split endpoint 4096 2331+point split endpoint 4096 2332)/2)
    have hp : upperPayment 2331 = (239896794306:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2331+point split endpoint 4096 2332)/2 = (634788777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634788777:ℝ)/168755200)*ClassicalSixthBranch.v ((634788777:ℝ)/168755200)/ClassicalSixthBranch.r = (107809780806945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2331
  · change upperPayment 2332 ≤ upperValue ((point split endpoint 4096 2332+point split endpoint 4096 2333)/2)
    have hp : upperPayment 2332 = (239789274994:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2332+point split endpoint 4096 2333)/2 = (634813927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634813927:ℝ)/168755200)*ClassicalSixthBranch.v ((634813927:ℝ)/168755200)/ClassicalSixthBranch.r = (107788483625985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2332
  · change upperPayment 2333 ≤ upperValue ((point split endpoint 4096 2333+point split endpoint 4096 2334)/2)
    have hp : upperPayment 2333 = (239681727623:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2333+point split endpoint 4096 2334)/2 = (634839077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634839077:ℝ)/168755200)*ClassicalSixthBranch.v ((634839077:ℝ)/168755200)/ClassicalSixthBranch.r = (107767188469097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2333
  · change upperPayment 2334 ≤ upperValue ((point split endpoint 4096 2334+point split endpoint 4096 2335)/2)
    have hp : upperPayment 2334 = (239574152188:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2334+point split endpoint 4096 2335)/2 = (634864227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634864227:ℝ)/168755200)*ClassicalSixthBranch.v ((634864227:ℝ)/168755200)/ClassicalSixthBranch.r = (107745895336281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2334
  · change upperPayment 2335 ≤ upperValue ((point split endpoint 4096 2335+point split endpoint 4096 2336)/2)
    have hp : upperPayment 2335 = (239466548681:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2335+point split endpoint 4096 2336)/2 = (634889377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((634889377:ℝ)/168755200)*ClassicalSixthBranch.v ((634889377:ℝ)/168755200)/ClassicalSixthBranch.r = (107724604227537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2335
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_145
