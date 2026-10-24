import WR2ClassicalFifthInitialPayments
import WR2ClassicalFifthInitialPoints041
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem initial_grid_block_041 (j : Fin 16) : initialPayment (16*41+j.val) ≤
    initialValue ((point lo 4 1024 (16*41+j.val)+point lo 4 1024 (16*41+j.val+1))/2) := by
  fin_cases j
  · change initialPayment 656 ≤ initialValue ((point lo 4 1024 656+point lo 4 1024 657)/2)
    have hp : initialPayment 656 = (335315235549:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 656+point lo 4 1024 657)/2 = (31976897:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((31976897:ℝ)/8437760) = (67942400:ℝ)/52095803 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_656
  · change initialPayment 657 ≤ initialValue ((point lo 4 1024 657+point lo 4 1024 658)/2)
    have hp : initialPayment 657 = (335984368877:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 657+point lo 4 1024 658)/2 = (159908623:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159908623:ℝ)/42188800) = (13588480:ℝ)/10414333 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_657
  · change initialPayment 658 ≤ initialValue ((point lo 4 1024 658+point lo 4 1024 659)/2)
    have hp : initialPayment 658 = (336654081358:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 658+point lo 4 1024 659)/2 = (159932761:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159932761:ℝ)/42188800) = (67942400:ℝ)/52047527 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_658
  · change initialPayment 659 ≤ initialValue ((point lo 4 1024 659+point lo 4 1024 660)/2)
    have hp : initialPayment 659 = (337324373549:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 659+point lo 4 1024 660)/2 = (159956899:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159956899:ℝ)/42188800) = (67942400:ℝ)/52023389 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_659
  · change initialPayment 660 ≤ initialValue ((point lo 4 1024 660+point lo 4 1024 661)/2)
    have hp : initialPayment 660 = (337995246009:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 660+point lo 4 1024 661)/2 = (159981037:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((159981037:ℝ)/42188800) = (67942400:ℝ)/51999251 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_660
  · change initialPayment 661 ≤ initialValue ((point lo 4 1024 661+point lo 4 1024 662)/2)
    have hp : initialPayment 661 = (338666699296:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 661+point lo 4 1024 662)/2 = (6400207:ℝ)/1687552 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((6400207:ℝ)/1687552) = (67942400:ℝ)/51975113 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_661
  · change initialPayment 662 ≤ initialValue ((point lo 4 1024 662+point lo 4 1024 663)/2)
    have hp : initialPayment 662 = (339338733970:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 662+point lo 4 1024 663)/2 = (160029313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160029313:ℝ)/42188800) = (2717696:ℝ)/2078039 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_662
  · change initialPayment 663 ≤ initialValue ((point lo 4 1024 663+point lo 4 1024 664)/2)
    have hp : initialPayment 663 = (340011350593:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 663+point lo 4 1024 664)/2 = (1553917:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((1553917:ℝ)/409600) = (51200:ℝ)/39131 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_663
  · change initialPayment 664 ≤ initialValue ((point lo 4 1024 664+point lo 4 1024 665)/2)
    have hp : initialPayment 664 = (340684549726:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 664+point lo 4 1024 665)/2 = (160077589:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160077589:ℝ)/42188800) = (67942400:ℝ)/51902699 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_664
  · change initialPayment 665 ≤ initialValue ((point lo 4 1024 665+point lo 4 1024 666)/2)
    have hp : initialPayment 665 = (341358331932:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 665+point lo 4 1024 666)/2 = (160101727:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160101727:ℝ)/42188800) = (67942400:ℝ)/51878561 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_665
  · change initialPayment 666 ≤ initialValue ((point lo 4 1024 666+point lo 4 1024 667)/2)
    have hp : initialPayment 666 = (342032697775:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 666+point lo 4 1024 667)/2 = (32025173:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32025173:ℝ)/8437760) = (67942400:ℝ)/51854423 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_666
  · change initialPayment 667 ≤ initialValue ((point lo 4 1024 667+point lo 4 1024 668)/2)
    have hp : initialPayment 667 = (342707647818:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 667+point lo 4 1024 668)/2 = (160150003:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160150003:ℝ)/42188800) = (13588480:ℝ)/10366057 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_667
  · change initialPayment 668 ≤ initialValue ((point lo 4 1024 668+point lo 4 1024 669)/2)
    have hp : initialPayment 668 = (343383182626:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 668+point lo 4 1024 669)/2 = (160174141:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160174141:ℝ)/42188800) = (67942400:ℝ)/51806147 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_668
  · change initialPayment 669 ≤ initialValue ((point lo 4 1024 669+point lo 4 1024 670)/2)
    have hp : initialPayment 669 = (344059302766:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 669+point lo 4 1024 670)/2 = (160198279:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160198279:ℝ)/42188800) = (67942400:ℝ)/51782009 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_669
  · change initialPayment 670 ≤ initialValue ((point lo 4 1024 670+point lo 4 1024 671)/2)
    have hp : initialPayment 670 = (344736008805:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 670+point lo 4 1024 671)/2 = (160222417:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((160222417:ℝ)/42188800) = (67942400:ℝ)/51757871 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_670
  · change initialPayment 671 ≤ initialValue ((point lo 4 1024 671+point lo 4 1024 672)/2)
    have hp : initialPayment 671 = (345413301311:ℝ)/1000000000000 := rfl
    have hx : (point lo 4 1024 671+point lo 4 1024 672)/2 = (32049311:ℝ)/8437760 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r/ClassicalSixthBranch.v ((32049311:ℝ)/8437760) = (67942400:ℝ)/51733733 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold initialValue
    rw [hr]
    exact paid_initial_671
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.initial_grid_block_041
