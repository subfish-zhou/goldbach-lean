import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints047
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_047 (j : Fin 16) : terminalPayment (16*47+j.val) ≤
    terminalValue ((point cut hi 1024 (16*47+j.val)+point cut hi 1024 (16*47+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 752 ≤ terminalValue ((point cut hi 1024 752+point cut hi 1024 753)/2)
    have hp : terminalPayment 752 = (256739754333:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 752+point cut hi 1024 753)/2 = (188716863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188716863:ℝ)/42188800) = (1960681:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188716863:ℝ)/42188800)-4 = (19961663:ℝ)/42188800 by norm_num]
    exact paid_terminal_752
  · change terminalPayment 753 ≤ terminalValue ((point cut hi 1024 753+point cut hi 1024 754)/2)
    have hp : terminalPayment 753 = (255934575330:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 753+point cut hi 1024 754)/2 = (188742013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188742013:ℝ)/42188800) = (1959675:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188742013:ℝ)/42188800)-4 = (19986813:ℝ)/42188800 by norm_num]
    exact paid_terminal_753
  · change terminalPayment 754 ≤ terminalValue ((point cut hi 1024 754+point cut hi 1024 755)/2)
    have hp : terminalPayment 754 = (255128479186:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 754+point cut hi 1024 755)/2 = (188767163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188767163:ℝ)/42188800) = (1958669:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188767163:ℝ)/42188800)-4 = (20011963:ℝ)/42188800 by norm_num]
    exact paid_terminal_754
  · change terminalPayment 755 ≤ terminalValue ((point cut hi 1024 755+point cut hi 1024 756)/2)
    have hp : terminalPayment 755 = (254321464708:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 755+point cut hi 1024 756)/2 = (188792313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188792313:ℝ)/42188800) = (1957663:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188792313:ℝ)/42188800)-4 = (20037113:ℝ)/42188800 by norm_num]
    exact paid_terminal_755
  · change terminalPayment 756 ≤ terminalValue ((point cut hi 1024 756+point cut hi 1024 757)/2)
    have hp : terminalPayment 756 = (253513530701:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 756+point cut hi 1024 757)/2 = (188817463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188817463:ℝ)/42188800) = (1956657:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188817463:ℝ)/42188800)-4 = (20062263:ℝ)/42188800 by norm_num]
    exact paid_terminal_756
  · change terminalPayment 757 ≤ terminalValue ((point cut hi 1024 757+point cut hi 1024 758)/2)
    have hp : terminalPayment 757 = (252704675966:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 757+point cut hi 1024 758)/2 = (188842613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188842613:ℝ)/42188800) = (1955651:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188842613:ℝ)/42188800)-4 = (20087413:ℝ)/42188800 by norm_num]
    exact paid_terminal_757
  · change terminalPayment 758 ≤ terminalValue ((point cut hi 1024 758+point cut hi 1024 759)/2)
    have hp : terminalPayment 758 = (251894899305:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 758+point cut hi 1024 759)/2 = (188867763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188867763:ℝ)/42188800) = (1954645:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188867763:ℝ)/42188800)-4 = (20112563:ℝ)/42188800 by norm_num]
    exact paid_terminal_758
  · change terminalPayment 759 ≤ terminalValue ((point cut hi 1024 759+point cut hi 1024 760)/2)
    have hp : terminalPayment 759 = (251084199515:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 759+point cut hi 1024 760)/2 = (188892913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188892913:ℝ)/42188800) = (1953639:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188892913:ℝ)/42188800)-4 = (20137713:ℝ)/42188800 by norm_num]
    exact paid_terminal_759
  · change terminalPayment 760 ≤ terminalValue ((point cut hi 1024 760+point cut hi 1024 761)/2)
    have hp : terminalPayment 760 = (250272575394:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 760+point cut hi 1024 761)/2 = (188918063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188918063:ℝ)/42188800) = (1952633:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188918063:ℝ)/42188800)-4 = (20162863:ℝ)/42188800 by norm_num]
    exact paid_terminal_760
  · change terminalPayment 761 ≤ terminalValue ((point cut hi 1024 761+point cut hi 1024 762)/2)
    have hp : terminalPayment 761 = (249460025734:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 761+point cut hi 1024 762)/2 = (188943213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188943213:ℝ)/42188800) = (1951627:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188943213:ℝ)/42188800)-4 = (20188013:ℝ)/42188800 by norm_num]
    exact paid_terminal_761
  · change terminalPayment 762 ≤ terminalValue ((point cut hi 1024 762+point cut hi 1024 763)/2)
    have hp : terminalPayment 762 = (248646549327:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 762+point cut hi 1024 763)/2 = (188968363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188968363:ℝ)/42188800) = (1950621:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188968363:ℝ)/42188800)-4 = (20213163:ℝ)/42188800 by norm_num]
    exact paid_terminal_762
  · change terminalPayment 763 ≤ terminalValue ((point cut hi 1024 763+point cut hi 1024 764)/2)
    have hp : terminalPayment 763 = (247832144964:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 763+point cut hi 1024 764)/2 = (188993513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188993513:ℝ)/42188800) = (1949615:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188993513:ℝ)/42188800)-4 = (20238313:ℝ)/42188800 by norm_num]
    exact paid_terminal_763
  · change terminalPayment 764 ≤ terminalValue ((point cut hi 1024 764+point cut hi 1024 765)/2)
    have hp : terminalPayment 764 = (247016811432:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 764+point cut hi 1024 765)/2 = (189018663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189018663:ℝ)/42188800) = (1948609:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189018663:ℝ)/42188800)-4 = (20263463:ℝ)/42188800 by norm_num]
    exact paid_terminal_764
  · change terminalPayment 765 ≤ terminalValue ((point cut hi 1024 765+point cut hi 1024 766)/2)
    have hp : terminalPayment 765 = (246200547517:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 765+point cut hi 1024 766)/2 = (189043813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189043813:ℝ)/42188800) = (1947603:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189043813:ℝ)/42188800)-4 = (20288613:ℝ)/42188800 by norm_num]
    exact paid_terminal_765
  · change terminalPayment 766 ≤ terminalValue ((point cut hi 1024 766+point cut hi 1024 767)/2)
    have hp : terminalPayment 766 = (245383352002:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 766+point cut hi 1024 767)/2 = (1835621:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((1835621:ℝ)/409600) = (18899:ℝ)/16384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((1835621:ℝ)/409600)-4 = (197221:ℝ)/409600 by norm_num]
    exact paid_terminal_766
  · change terminalPayment 767 ≤ terminalValue ((point cut hi 1024 767+point cut hi 1024 768)/2)
    have hp : terminalPayment 767 = (244565223669:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 767+point cut hi 1024 768)/2 = (189094113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189094113:ℝ)/42188800) = (1945591:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189094113:ℝ)/42188800)-4 = (20338913:ℝ)/42188800 by norm_num]
    exact paid_terminal_767
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_047
