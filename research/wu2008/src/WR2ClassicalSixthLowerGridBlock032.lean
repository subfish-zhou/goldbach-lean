import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints032
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_032 (j : Fin 16) : lowerPayment (16*32+j.val) ≤
    lowerValue ((point 2 split 4096 (16*32+j.val)+point 2 split 4096 (16*32+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 512 ≤ lowerValue ((point 2 split 4096 512+point 2 split 4096 513)/2)
    have hp : lowerPayment 512 = (74706867024:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 512+point 2 split 4096 513)/2 = (14694787:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((14694787:ℝ)/6750208)/ClassicalSixthBranch.v ((14694787:ℝ)/6750208) = (774391918779:ℝ)/395974417048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_512
  · change lowerPayment 513 ≤ lowerValue ((point 2 split 4096 513+point 2 split 4096 514)/2)
    have hp : lowerPayment 513 = (74837678304:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 513+point 2 split 4096 514)/2 = (367427937:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367427937:ℝ)/168755200)/ClassicalSixthBranch.v ((367427937:ℝ)/168755200) = (154862921021:ℝ)/79185281832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_513
  · change lowerPayment 514 ≤ lowerValue ((point 2 split 4096 514+point 2 split 4096 515)/2)
    have hp : lowerPayment 514 = (74968439881:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 514+point 2 split 4096 515)/2 = (367486199:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367486199:ℝ)/168755200)/ClassicalSixthBranch.v ((367486199:ℝ)/168755200) = (774237291431:ℝ)/395878401272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_514
  · change lowerPayment 515 ≤ lowerValue ((point 2 split 4096 515+point 2 split 4096 516)/2)
    have hp : lowerPayment 515 = (75099151799:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 515+point 2 split 4096 516)/2 = (367544461:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367544461:ℝ)/168755200)/ClassicalSixthBranch.v ((367544461:ℝ)/168755200) = (774159977757:ℝ)/395830393384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_515
  · change lowerPayment 516 ≤ lowerValue ((point 2 split 4096 516+point 2 split 4096 517)/2)
    have hp : lowerPayment 516 = (75229814102:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 516+point 2 split 4096 517)/2 = (367602723:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367602723:ℝ)/168755200)/ClassicalSixthBranch.v ((367602723:ℝ)/168755200) = (774082664083:ℝ)/395782385496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_516
  · change lowerPayment 517 ≤ lowerValue ((point 2 split 4096 517+point 2 split 4096 518)/2)
    have hp : lowerPayment 517 = (75360426835:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 517+point 2 split 4096 518)/2 = (73532197:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73532197:ℝ)/33751040)/ClassicalSixthBranch.v ((73532197:ℝ)/33751040) = (774005350409:ℝ)/395734377608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_517
  · change lowerPayment 518 ≤ lowerValue ((point 2 split 4096 518+point 2 split 4096 519)/2)
    have hp : lowerPayment 518 = (75490990041:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 518+point 2 split 4096 519)/2 = (367719247:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367719247:ℝ)/168755200)/ClassicalSixthBranch.v ((367719247:ℝ)/168755200) = (154785607347:ℝ)/79137273944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_518
  · change lowerPayment 519 ≤ lowerValue ((point 2 split 4096 519+point 2 split 4096 520)/2)
    have hp : lowerPayment 519 = (75621503764:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 519+point 2 split 4096 520)/2 = (367777509:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367777509:ℝ)/168755200)/ClassicalSixthBranch.v ((367777509:ℝ)/168755200) = (773850723061:ℝ)/395638361832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_519
  · change lowerPayment 520 ≤ lowerValue ((point 2 split 4096 520+point 2 split 4096 521)/2)
    have hp : lowerPayment 520 = (75751968048:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 520+point 2 split 4096 521)/2 = (367835771:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367835771:ℝ)/168755200)/ClassicalSixthBranch.v ((367835771:ℝ)/168755200) = (773773409387:ℝ)/395590353944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_520
  · change lowerPayment 521 ≤ lowerValue ((point 2 split 4096 521+point 2 split 4096 522)/2)
    have hp : lowerPayment 521 = (75882382937:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 521+point 2 split 4096 522)/2 = (367894033:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((367894033:ℝ)/168755200)/ClassicalSixthBranch.v ((367894033:ℝ)/168755200) = (773696095713:ℝ)/395542346056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_521
  · change lowerPayment 522 ≤ lowerValue ((point 2 split 4096 522+point 2 split 4096 523)/2)
    have hp : lowerPayment 522 = (76012748475:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 522+point 2 split 4096 523)/2 = (73590459:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73590459:ℝ)/33751040)/ClassicalSixthBranch.v ((73590459:ℝ)/33751040) = (773618782039:ℝ)/395494338168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_522
  · change lowerPayment 523 ≤ lowerValue ((point 2 split 4096 523+point 2 split 4096 524)/2)
    have hp : lowerPayment 523 = (76143064705:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 523+point 2 split 4096 524)/2 = (368010557:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368010557:ℝ)/168755200)/ClassicalSixthBranch.v ((368010557:ℝ)/168755200) = (154708293673:ℝ)/79089266056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_523
  · change lowerPayment 524 ≤ lowerValue ((point 2 split 4096 524+point 2 split 4096 525)/2)
    have hp : lowerPayment 524 = (76273331672:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 524+point 2 split 4096 525)/2 = (368068819:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368068819:ℝ)/168755200)/ClassicalSixthBranch.v ((368068819:ℝ)/168755200) = (773464154691:ℝ)/395398322392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_524
  · change lowerPayment 525 ≤ lowerValue ((point 2 split 4096 525+point 2 split 4096 526)/2)
    have hp : lowerPayment 525 = (76403549419:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 525+point 2 split 4096 526)/2 = (368127081:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368127081:ℝ)/168755200)/ClassicalSixthBranch.v ((368127081:ℝ)/168755200) = (773386841017:ℝ)/395350314504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_525
  · change lowerPayment 526 ≤ lowerValue ((point 2 split 4096 526+point 2 split 4096 527)/2)
    have hp : lowerPayment 526 = (76533717989:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 526+point 2 split 4096 527)/2 = (368185343:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((368185343:ℝ)/168755200)/ClassicalSixthBranch.v ((368185343:ℝ)/168755200) = (773309527343:ℝ)/395302306616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_526
  · change lowerPayment 527 ≤ lowerValue ((point 2 split 4096 527+point 2 split 4096 528)/2)
    have hp : lowerPayment 527 = (76663837427:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 527+point 2 split 4096 528)/2 = (73648721:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((73648721:ℝ)/33751040)/ClassicalSixthBranch.v ((73648721:ℝ)/33751040) = (773232213669:ℝ)/395254298728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_527
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_032
