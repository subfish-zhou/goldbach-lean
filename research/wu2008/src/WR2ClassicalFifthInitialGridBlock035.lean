import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints035
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_035 (j : Fin 16) : initialPayment (16*35+j.val) ≤
    initialValue ((point lo 4 1024 (16*35+j.val)+point lo 4 1024 (16*35+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 560 ≤ initialValue ((point lo 4 1024 560+point lo 4 1024 561)/2)
    have hp : initialPayment 560 = (273693247840:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 560+point lo 4 1024 561)/2 = (1529779:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((1529779:ℝ)/409600) = (67942400:ℝ)/54413051 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_560
  · change initialPayment 561 ≤ initialValue ((point lo 4 1024 561+point lo 4 1024 562)/2)
    have hp : initialPayment 561 = (274309255130:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 561+point lo 4 1024 562)/2 = (6303655:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6303655:ℝ)/1687552) = (67942400:ℝ)/54388913 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_561
  · change initialPayment 562 ≤ initialValue ((point lo 4 1024 562+point lo 4 1024 563)/2)
    have hp : initialPayment 562 = (274925791773:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 562+point lo 4 1024 563)/2 = (157615513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157615513:ℝ)/42188800) = (2717696:ℝ)/2174591 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_562
  · change initialPayment 563 ≤ initialValue ((point lo 4 1024 563+point lo 4 1024 564)/2)
    have hp : initialPayment 563 = (275542858250:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 563+point lo 4 1024 564)/2 = (157639651:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157639651:ℝ)/42188800) = (67942400:ℝ)/54340637 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_563
  · change initialPayment 564 ≤ initialValue ((point lo 4 1024 564+point lo 4 1024 565)/2)
    have hp : initialPayment 564 = (276160455046:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 564+point lo 4 1024 565)/2 = (157663789:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157663789:ℝ)/42188800) = (67942400:ℝ)/54316499 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_564
  · change initialPayment 565 ≤ initialValue ((point lo 4 1024 565+point lo 4 1024 566)/2)
    have hp : initialPayment 565 = (276778582644:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 565+point lo 4 1024 566)/2 = (157687927:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157687927:ℝ)/42188800) = (67942400:ℝ)/54292361 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_565
  · change initialPayment 566 ≤ initialValue ((point lo 4 1024 566+point lo 4 1024 567)/2)
    have hp : initialPayment 566 = (277397241531:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 566+point lo 4 1024 567)/2 = (31542413:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31542413:ℝ)/8437760) = (67942400:ℝ)/54268223 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_566
  · change initialPayment 567 ≤ initialValue ((point lo 4 1024 567+point lo 4 1024 568)/2)
    have hp : initialPayment 567 = (278016432190:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 567+point lo 4 1024 568)/2 = (157736203:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157736203:ℝ)/42188800) = (13588480:ℝ)/10848817 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_567
  · change initialPayment 568 ≤ initialValue ((point lo 4 1024 568+point lo 4 1024 569)/2)
    have hp : initialPayment 568 = (278636155110:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 568+point lo 4 1024 569)/2 = (157760341:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157760341:ℝ)/42188800) = (67942400:ℝ)/54219947 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_568
  · change initialPayment 569 ≤ initialValue ((point lo 4 1024 569+point lo 4 1024 570)/2)
    have hp : initialPayment 569 = (279256410776:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 569+point lo 4 1024 570)/2 = (157784479:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157784479:ℝ)/42188800) = (67942400:ℝ)/54195809 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_569
  · change initialPayment 570 ≤ initialValue ((point lo 4 1024 570+point lo 4 1024 571)/2)
    have hp : initialPayment 570 = (279877199677:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 570+point lo 4 1024 571)/2 = (157808617:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157808617:ℝ)/42188800) = (67942400:ℝ)/54171671 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_570
  · change initialPayment 571 ≤ initialValue ((point lo 4 1024 571+point lo 4 1024 572)/2)
    have hp : initialPayment 571 = (280498522302:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 571+point lo 4 1024 572)/2 = (31566551:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31566551:ℝ)/8437760) = (67942400:ℝ)/54147533 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_571
  · change initialPayment 572 ≤ initialValue ((point lo 4 1024 572+point lo 4 1024 573)/2)
    have hp : initialPayment 572 = (281120379139:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 572+point lo 4 1024 573)/2 = (157856893:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157856893:ℝ)/42188800) = (13588480:ℝ)/10824679 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_572
  · change initialPayment 573 ≤ initialValue ((point lo 4 1024 573+point lo 4 1024 574)/2)
    have hp : initialPayment 573 = (281742770679:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 573+point lo 4 1024 574)/2 = (157881031:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157881031:ℝ)/42188800) = (67942400:ℝ)/54099257 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_573
  · change initialPayment 574 ≤ initialValue ((point lo 4 1024 574+point lo 4 1024 575)/2)
    have hp : initialPayment 574 = (282365697412:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 574+point lo 4 1024 575)/2 = (157905169:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157905169:ℝ)/42188800) = (67942400:ℝ)/54075119 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_574
  · change initialPayment 575 ≤ initialValue ((point lo 4 1024 575+point lo 4 1024 576)/2)
    have hp : initialPayment 575 = (282989159830:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 575+point lo 4 1024 576)/2 = (157929307:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((157929307:ℝ)/42188800) = (67942400:ℝ)/54050981 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_575
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_035
