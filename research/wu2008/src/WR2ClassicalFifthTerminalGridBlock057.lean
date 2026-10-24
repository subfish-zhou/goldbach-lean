import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints057
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_057 (j : Fin 16) : terminalPayment (16*57+j.val) ≤
    terminalValue ((point cut hi 1024 (16*57+j.val)+point cut hi 1024 (16*57+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 912 ≤ terminalValue ((point cut hi 1024 912+point cut hi 1024 913)/2)
    have hp : terminalPayment 912 = (115386972803:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 912+point cut hi 1024 913)/2 = (192740863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192740863:ℝ)/42188800) = (1799721:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192740863:ℝ)/42188800)-4 = (23985663:ℝ)/42188800 by norm_num]
    exact paid_terminal_912
  · change terminalPayment 913 ≤ terminalValue ((point cut hi 1024 913+point cut hi 1024 914)/2)
    have hp : terminalPayment 913 = (114418351014:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 913+point cut hi 1024 914)/2 = (192766013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192766013:ℝ)/42188800) = (1798715:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192766013:ℝ)/42188800)-4 = (24010813:ℝ)/42188800 by norm_num]
    exact paid_terminal_913
  · change terminalPayment 914 ≤ terminalValue ((point cut hi 1024 914+point cut hi 1024 915)/2)
    have hp : terminalPayment 914 = (113448591413:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 914+point cut hi 1024 915)/2 = (192791163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192791163:ℝ)/42188800) = (1797709:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192791163:ℝ)/42188800)-4 = (24035963:ℝ)/42188800 by norm_num]
    exact paid_terminal_914
  · change terminalPayment 915 ≤ terminalValue ((point cut hi 1024 915+point cut hi 1024 916)/2)
    have hp : terminalPayment 915 = (112477692411:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 915+point cut hi 1024 916)/2 = (192816313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192816313:ℝ)/42188800) = (1796703:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192816313:ℝ)/42188800)-4 = (24061113:ℝ)/42188800 by norm_num]
    exact paid_terminal_915
  · change terminalPayment 916 ≤ terminalValue ((point cut hi 1024 916+point cut hi 1024 917)/2)
    have hp : terminalPayment 916 = (111505652414:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 916+point cut hi 1024 917)/2 = (192841463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192841463:ℝ)/42188800) = (1795697:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192841463:ℝ)/42188800)-4 = (24086263:ℝ)/42188800 by norm_num]
    exact paid_terminal_916
  · change terminalPayment 917 ≤ terminalValue ((point cut hi 1024 917+point cut hi 1024 918)/2)
    have hp : terminalPayment 917 = (110532469827:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 917+point cut hi 1024 918)/2 = (192866613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192866613:ℝ)/42188800) = (1794691:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192866613:ℝ)/42188800)-4 = (24111413:ℝ)/42188800 by norm_num]
    exact paid_terminal_917
  · change terminalPayment 918 ≤ terminalValue ((point cut hi 1024 918+point cut hi 1024 919)/2)
    have hp : terminalPayment 918 = (109558143052:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 918+point cut hi 1024 919)/2 = (192891763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192891763:ℝ)/42188800) = (1793685:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192891763:ℝ)/42188800)-4 = (24136563:ℝ)/42188800 by norm_num]
    exact paid_terminal_918
  · change terminalPayment 919 ≤ terminalValue ((point cut hi 1024 919+point cut hi 1024 920)/2)
    have hp : terminalPayment 919 = (108582670486:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 919+point cut hi 1024 920)/2 = (192916913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192916913:ℝ)/42188800) = (1792679:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192916913:ℝ)/42188800)-4 = (24161713:ℝ)/42188800 by norm_num]
    exact paid_terminal_919
  · change terminalPayment 920 ≤ terminalValue ((point cut hi 1024 920+point cut hi 1024 921)/2)
    have hp : terminalPayment 920 = (107606050524:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 920+point cut hi 1024 921)/2 = (192942063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192942063:ℝ)/42188800) = (1791673:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192942063:ℝ)/42188800)-4 = (24186863:ℝ)/42188800 by norm_num]
    exact paid_terminal_920
  · change terminalPayment 921 ≤ terminalValue ((point cut hi 1024 921+point cut hi 1024 922)/2)
    have hp : terminalPayment 921 = (106628281560:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 921+point cut hi 1024 922)/2 = (192967213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192967213:ℝ)/42188800) = (1790667:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192967213:ℝ)/42188800)-4 = (24212013:ℝ)/42188800 by norm_num]
    exact paid_terminal_921
  · change terminalPayment 922 ≤ terminalValue ((point cut hi 1024 922+point cut hi 1024 923)/2)
    have hp : terminalPayment 922 = (105649361982:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 922+point cut hi 1024 923)/2 = (192992363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192992363:ℝ)/42188800) = (1789661:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192992363:ℝ)/42188800)-4 = (24237163:ℝ)/42188800 by norm_num]
    exact paid_terminal_922
  · change terminalPayment 923 ≤ terminalValue ((point cut hi 1024 923+point cut hi 1024 924)/2)
    have hp : terminalPayment 923 = (104669290177:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 923+point cut hi 1024 924)/2 = (193017513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193017513:ℝ)/42188800) = (1788655:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193017513:ℝ)/42188800)-4 = (24262313:ℝ)/42188800 by norm_num]
    exact paid_terminal_923
  · change terminalPayment 924 ≤ terminalValue ((point cut hi 1024 924+point cut hi 1024 925)/2)
    have hp : terminalPayment 924 = (103688064528:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 924+point cut hi 1024 925)/2 = (193042663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193042663:ℝ)/42188800) = (1787649:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193042663:ℝ)/42188800)-4 = (24287463:ℝ)/42188800 by norm_num]
    exact paid_terminal_924
  · change terminalPayment 925 ≤ terminalValue ((point cut hi 1024 925+point cut hi 1024 926)/2)
    have hp : terminalPayment 925 = (102705683416:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 925+point cut hi 1024 926)/2 = (193067813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193067813:ℝ)/42188800) = (1786643:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193067813:ℝ)/42188800)-4 = (24312613:ℝ)/42188800 by norm_num]
    exact paid_terminal_925
  · change terminalPayment 926 ≤ terminalValue ((point cut hi 1024 926+point cut hi 1024 927)/2)
    have hp : terminalPayment 926 = (101722145218:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 926+point cut hi 1024 927)/2 = (193092963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193092963:ℝ)/42188800) = (1785637:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193092963:ℝ)/42188800)-4 = (24337763:ℝ)/42188800 by norm_num]
    exact paid_terminal_926
  · change terminalPayment 927 ≤ terminalValue ((point cut hi 1024 927+point cut hi 1024 928)/2)
    have hp : terminalPayment 927 = (100737448309:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 927+point cut hi 1024 928)/2 = (193118113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193118113:ℝ)/42188800) = (1784631:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193118113:ℝ)/42188800)-4 = (24362913:ℝ)/42188800 by norm_num]
    exact paid_terminal_927
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_057
