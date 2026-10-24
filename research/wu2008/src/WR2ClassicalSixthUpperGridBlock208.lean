import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints208
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_208 (j : Fin 16) : upperPayment (16*208+j.val) ≤
    upperValue ((point split endpoint 4096 (16*208+j.val)+point split endpoint 4096 (16*208+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3328 ≤ upperValue ((point split endpoint 4096 3328+point split endpoint 4096 3329)/2)
    have hp : upperPayment 3328 = (117688772767:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3328+point split endpoint 4096 3329)/2 = (659863327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659863327:ℝ)/168755200)*ClassicalSixthBranch.v ((659863327:ℝ)/168755200)/ClassicalSixthBranch.r = (87581455282257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3328
  · change upperPayment 3329 ≤ upperValue ((point split endpoint 4096 3329+point split endpoint 4096 3330)/2)
    have hp : upperPayment 3329 = (117549906936:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3329+point split endpoint 4096 3330)/2 = (659888477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659888477:ℝ)/168755200)*ClassicalSixthBranch.v ((659888477:ℝ)/168755200)/ClassicalSixthBranch.r = (87562176101081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3329
  · change upperPayment 3330 ≤ upperValue ((point split endpoint 4096 3330+point split endpoint 4096 3331)/2)
    have hp : upperPayment 3330 = (117411005789:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3330+point split endpoint 4096 3331)/2 = (659913627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659913627:ℝ)/168755200)*ClassicalSixthBranch.v ((659913627:ℝ)/168755200)/ClassicalSixthBranch.r = (87542898943977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3330
  · change upperPayment 3331 ≤ upperValue ((point split endpoint 4096 3331+point split endpoint 4096 3332)/2)
    have hp : upperPayment 3331 = (117272069316:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3331+point split endpoint 4096 3332)/2 = (659938777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659938777:ℝ)/168755200)*ClassicalSixthBranch.v ((659938777:ℝ)/168755200)/ClassicalSixthBranch.r = (87523623810945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3331
  · change upperPayment 3332 ≤ upperValue ((point split endpoint 4096 3332+point split endpoint 4096 3333)/2)
    have hp : upperPayment 3332 = (117133097510:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3332+point split endpoint 4096 3333)/2 = (659963927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659963927:ℝ)/168755200)*ClassicalSixthBranch.v ((659963927:ℝ)/168755200)/ClassicalSixthBranch.r = (87504350701985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3332
  · change upperPayment 3333 ≤ upperValue ((point split endpoint 4096 3333+point split endpoint 4096 3334)/2)
    have hp : upperPayment 3333 = (116994090360:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3333+point split endpoint 4096 3334)/2 = (659989077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((659989077:ℝ)/168755200)*ClassicalSixthBranch.v ((659989077:ℝ)/168755200)/ClassicalSixthBranch.r = (87485079617097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3333
  · change upperPayment 3334 ≤ upperValue ((point split endpoint 4096 3334+point split endpoint 4096 3335)/2)
    have hp : upperPayment 3334 = (116855047859:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3334+point split endpoint 4096 3335)/2 = (660014227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660014227:ℝ)/168755200)*ClassicalSixthBranch.v ((660014227:ℝ)/168755200)/ClassicalSixthBranch.r = (87465810556281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3334
  · change upperPayment 3335 ≤ upperValue ((point split endpoint 4096 3335+point split endpoint 4096 3336)/2)
    have hp : upperPayment 3335 = (116715969997:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3335+point split endpoint 4096 3336)/2 = (660039377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660039377:ℝ)/168755200)*ClassicalSixthBranch.v ((660039377:ℝ)/168755200)/ClassicalSixthBranch.r = (87446543519537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3335
  · change upperPayment 3336 ≤ upperValue ((point split endpoint 4096 3336+point split endpoint 4096 3337)/2)
    have hp : upperPayment 3336 = (116576856765:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3336+point split endpoint 4096 3337)/2 = (660064527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660064527:ℝ)/168755200)*ClassicalSixthBranch.v ((660064527:ℝ)/168755200)/ClassicalSixthBranch.r = (87427278506865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3336
  · change upperPayment 3337 ≤ upperValue ((point split endpoint 4096 3337+point split endpoint 4096 3338)/2)
    have hp : upperPayment 3337 = (116437708155:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3337+point split endpoint 4096 3338)/2 = (660089677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660089677:ℝ)/168755200)*ClassicalSixthBranch.v ((660089677:ℝ)/168755200)/ClassicalSixthBranch.r = (87408015518265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3337
  · change upperPayment 3338 ≤ upperValue ((point split endpoint 4096 3338+point split endpoint 4096 3339)/2)
    have hp : upperPayment 3338 = (116298524158:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3338+point split endpoint 4096 3339)/2 = (660114827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660114827:ℝ)/168755200)*ClassicalSixthBranch.v ((660114827:ℝ)/168755200)/ClassicalSixthBranch.r = (87388754553737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3338
  · change upperPayment 3339 ≤ upperValue ((point split endpoint 4096 3339+point split endpoint 4096 3340)/2)
    have hp : upperPayment 3339 = (116159304764:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3339+point split endpoint 4096 3340)/2 = (660139977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660139977:ℝ)/168755200)*ClassicalSixthBranch.v ((660139977:ℝ)/168755200)/ClassicalSixthBranch.r = (87369495613281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3339
  · change upperPayment 3340 ≤ upperValue ((point split endpoint 4096 3340+point split endpoint 4096 3341)/2)
    have hp : upperPayment 3340 = (116020049966:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3340+point split endpoint 4096 3341)/2 = (660165127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660165127:ℝ)/168755200)*ClassicalSixthBranch.v ((660165127:ℝ)/168755200)/ClassicalSixthBranch.r = (87350238696897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3340
  · change upperPayment 3341 ≤ upperValue ((point split endpoint 4096 3341+point split endpoint 4096 3342)/2)
    have hp : upperPayment 3341 = (115880759753:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3341+point split endpoint 4096 3342)/2 = (660190277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660190277:ℝ)/168755200)*ClassicalSixthBranch.v ((660190277:ℝ)/168755200)/ClassicalSixthBranch.r = (87330983804585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3341
  · change upperPayment 3342 ≤ upperValue ((point split endpoint 4096 3342+point split endpoint 4096 3343)/2)
    have hp : upperPayment 3342 = (115741434118:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3342+point split endpoint 4096 3343)/2 = (660215427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660215427:ℝ)/168755200)*ClassicalSixthBranch.v ((660215427:ℝ)/168755200)/ClassicalSixthBranch.r = (87311730936345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3342
  · change upperPayment 3343 ≤ upperValue ((point split endpoint 4096 3343+point split endpoint 4096 3344)/2)
    have hp : upperPayment 3343 = (115602073051:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3343+point split endpoint 4096 3344)/2 = (660240577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((660240577:ℝ)/168755200)*ClassicalSixthBranch.v ((660240577:ℝ)/168755200)/ClassicalSixthBranch.r = (87292480092177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3343
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_208
