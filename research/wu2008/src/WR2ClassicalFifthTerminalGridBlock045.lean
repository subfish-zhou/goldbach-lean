import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints045
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_045 (j : Fin 16) : terminalPayment (16*45+j.val) ≤
    terminalValue ((point cut hi 1024 (16*45+j.val)+point cut hi 1024 (16*45+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 720 ≤ terminalValue ((point cut hi 1024 720+point cut hi 1024 721)/2)
    have hp : terminalPayment 720 = (282028265579:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 720+point cut hi 1024 721)/2 = (187912063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187912063:ℝ)/42188800) = (1992873:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187912063:ℝ)/42188800)-4 = (19156863:ℝ)/42188800 by norm_num]
    exact paid_terminal_720
  · change terminalPayment 721 ≤ terminalValue ((point cut hi 1024 721+point cut hi 1024 722)/2)
    have hp : terminalPayment 721 = (281251817250:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 721+point cut hi 1024 722)/2 = (187937213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187937213:ℝ)/42188800) = (1991867:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187937213:ℝ)/42188800)-4 = (19182013:ℝ)/42188800 by norm_num]
    exact paid_terminal_721
  · change terminalPayment 722 ≤ terminalValue ((point cut hi 1024 722+point cut hi 1024 723)/2)
    have hp : terminalPayment 722 = (280474488892:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 722+point cut hi 1024 723)/2 = (187962363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187962363:ℝ)/42188800) = (1990861:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187962363:ℝ)/42188800)-4 = (19207163:ℝ)/42188800 by norm_num]
    exact paid_terminal_722
  · change terminalPayment 723 ≤ terminalValue ((point cut hi 1024 723+point cut hi 1024 724)/2)
    have hp : terminalPayment 723 = (279696279374:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 723+point cut hi 1024 724)/2 = (187987513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187987513:ℝ)/42188800) = (1989855:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187987513:ℝ)/42188800)-4 = (19232313:ℝ)/42188800 by norm_num]
    exact paid_terminal_723
  · change terminalPayment 724 ≤ terminalValue ((point cut hi 1024 724+point cut hi 1024 725)/2)
    have hp : terminalPayment 724 = (278917187567:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 724+point cut hi 1024 725)/2 = (188012663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188012663:ℝ)/42188800) = (1988849:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188012663:ℝ)/42188800)-4 = (19257463:ℝ)/42188800 by norm_num]
    exact paid_terminal_724
  · change terminalPayment 725 ≤ terminalValue ((point cut hi 1024 725+point cut hi 1024 726)/2)
    have hp : terminalPayment 725 = (278137212338:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 725+point cut hi 1024 726)/2 = (188037813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188037813:ℝ)/42188800) = (1987843:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188037813:ℝ)/42188800)-4 = (19282613:ℝ)/42188800 by norm_num]
    exact paid_terminal_725
  · change terminalPayment 726 ≤ terminalValue ((point cut hi 1024 726+point cut hi 1024 727)/2)
    have hp : terminalPayment 726 = (277356352551:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 726+point cut hi 1024 727)/2 = (188062963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188062963:ℝ)/42188800) = (1986837:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188062963:ℝ)/42188800)-4 = (19307763:ℝ)/42188800 by norm_num]
    exact paid_terminal_726
  · change terminalPayment 727 ≤ terminalValue ((point cut hi 1024 727+point cut hi 1024 728)/2)
    have hp : terminalPayment 727 = (276574607071:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 727+point cut hi 1024 728)/2 = (188088113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188088113:ℝ)/42188800) = (1985831:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188088113:ℝ)/42188800)-4 = (19332913:ℝ)/42188800 by norm_num]
    exact paid_terminal_727
  · change terminalPayment 728 ≤ terminalValue ((point cut hi 1024 728+point cut hi 1024 729)/2)
    have hp : terminalPayment 728 = (275791974759:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 728+point cut hi 1024 729)/2 = (188113263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188113263:ℝ)/42188800) = (1984825:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188113263:ℝ)/42188800)-4 = (19358063:ℝ)/42188800 by norm_num]
    exact paid_terminal_728
  · change terminalPayment 729 ≤ terminalValue ((point cut hi 1024 729+point cut hi 1024 730)/2)
    have hp : terminalPayment 729 = (275008454474:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 729+point cut hi 1024 730)/2 = (188138413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188138413:ℝ)/42188800) = (1983819:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188138413:ℝ)/42188800)-4 = (19383213:ℝ)/42188800 by norm_num]
    exact paid_terminal_729
  · change terminalPayment 730 ≤ terminalValue ((point cut hi 1024 730+point cut hi 1024 731)/2)
    have hp : terminalPayment 730 = (274224045074:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 730+point cut hi 1024 731)/2 = (188163563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188163563:ℝ)/42188800) = (1982813:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188163563:ℝ)/42188800)-4 = (19408363:ℝ)/42188800 by norm_num]
    exact paid_terminal_730
  · change terminalPayment 731 ≤ terminalValue ((point cut hi 1024 731+point cut hi 1024 732)/2)
    have hp : terminalPayment 731 = (273438745414:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 731+point cut hi 1024 732)/2 = (188188713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188188713:ℝ)/42188800) = (1981807:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188188713:ℝ)/42188800)-4 = (19433513:ℝ)/42188800 by norm_num]
    exact paid_terminal_731
  · change terminalPayment 732 ≤ terminalValue ((point cut hi 1024 732+point cut hi 1024 733)/2)
    have hp : terminalPayment 732 = (272652554348:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 732+point cut hi 1024 733)/2 = (188213863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188213863:ℝ)/42188800) = (1980801:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188213863:ℝ)/42188800)-4 = (19458663:ℝ)/42188800 by norm_num]
    exact paid_terminal_732
  · change terminalPayment 733 ≤ terminalValue ((point cut hi 1024 733+point cut hi 1024 734)/2)
    have hp : terminalPayment 733 = (271865470728:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 733+point cut hi 1024 734)/2 = (188239013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188239013:ℝ)/42188800) = (1979795:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188239013:ℝ)/42188800)-4 = (19483813:ℝ)/42188800 by norm_num]
    exact paid_terminal_733
  · change terminalPayment 734 ≤ terminalValue ((point cut hi 1024 734+point cut hi 1024 735)/2)
    have hp : terminalPayment 734 = (271077493402:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 734+point cut hi 1024 735)/2 = (188264163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188264163:ℝ)/42188800) = (1978789:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188264163:ℝ)/42188800)-4 = (19508963:ℝ)/42188800 by norm_num]
    exact paid_terminal_734
  · change terminalPayment 735 ≤ terminalValue ((point cut hi 1024 735+point cut hi 1024 736)/2)
    have hp : terminalPayment 735 = (270288621219:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 735+point cut hi 1024 736)/2 = (188289313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188289313:ℝ)/42188800) = (1977783:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188289313:ℝ)/42188800)-4 = (19534113:ℝ)/42188800 by norm_num]
    exact paid_terminal_735
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_045
