import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints046
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_046 (j : Fin 16) : terminalPayment (16*46+j.val) ≤
    terminalValue ((point cut hi 1024 (16*46+j.val)+point cut hi 1024 (16*46+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 736 ≤ terminalValue ((point cut hi 1024 736+point cut hi 1024 737)/2)
    have hp : terminalPayment 736 = (269498853023:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 736+point cut hi 1024 737)/2 = (188314463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188314463:ℝ)/42188800) = (1976777:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188314463:ℝ)/42188800)-4 = (19559263:ℝ)/42188800 by norm_num]
    exact paid_terminal_736
  · change terminalPayment 737 ≤ terminalValue ((point cut hi 1024 737+point cut hi 1024 738)/2)
    have hp : terminalPayment 737 = (268708187659:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 737+point cut hi 1024 738)/2 = (188339613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188339613:ℝ)/42188800) = (1975771:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188339613:ℝ)/42188800)-4 = (19584413:ℝ)/42188800 by norm_num]
    exact paid_terminal_737
  · change terminalPayment 738 ≤ terminalValue ((point cut hi 1024 738+point cut hi 1024 739)/2)
    have hp : terminalPayment 738 = (267916623967:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 738+point cut hi 1024 739)/2 = (188364763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188364763:ℝ)/42188800) = (1974765:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188364763:ℝ)/42188800)-4 = (19609563:ℝ)/42188800 by norm_num]
    exact paid_terminal_738
  · change terminalPayment 739 ≤ terminalValue ((point cut hi 1024 739+point cut hi 1024 740)/2)
    have hp : terminalPayment 739 = (267124160788:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 739+point cut hi 1024 740)/2 = (188389913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188389913:ℝ)/42188800) = (1973759:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188389913:ℝ)/42188800)-4 = (19634713:ℝ)/42188800 by norm_num]
    exact paid_terminal_739
  · change terminalPayment 740 ≤ terminalValue ((point cut hi 1024 740+point cut hi 1024 741)/2)
    have hp : terminalPayment 740 = (266330796958:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 740+point cut hi 1024 741)/2 = (188415063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188415063:ℝ)/42188800) = (1972753:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188415063:ℝ)/42188800)-4 = (19659863:ℝ)/42188800 by norm_num]
    exact paid_terminal_740
  · change terminalPayment 741 ≤ terminalValue ((point cut hi 1024 741+point cut hi 1024 742)/2)
    have hp : terminalPayment 741 = (265536531314:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 741+point cut hi 1024 742)/2 = (188440213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188440213:ℝ)/42188800) = (1971747:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188440213:ℝ)/42188800)-4 = (19685013:ℝ)/42188800 by norm_num]
    exact paid_terminal_741
  · change terminalPayment 742 ≤ terminalValue ((point cut hi 1024 742+point cut hi 1024 743)/2)
    have hp : terminalPayment 742 = (264741362688:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 742+point cut hi 1024 743)/2 = (188465363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188465363:ℝ)/42188800) = (1970741:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188465363:ℝ)/42188800)-4 = (19710163:ℝ)/42188800 by norm_num]
    exact paid_terminal_742
  · change terminalPayment 743 ≤ terminalValue ((point cut hi 1024 743+point cut hi 1024 744)/2)
    have hp : terminalPayment 743 = (263945289912:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 743+point cut hi 1024 744)/2 = (188490513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188490513:ℝ)/42188800) = (1969735:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188490513:ℝ)/42188800)-4 = (19735313:ℝ)/42188800 by norm_num]
    exact paid_terminal_743
  · change terminalPayment 744 ≤ terminalValue ((point cut hi 1024 744+point cut hi 1024 745)/2)
    have hp : terminalPayment 744 = (263148311815:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 744+point cut hi 1024 745)/2 = (188515663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188515663:ℝ)/42188800) = (1968729:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188515663:ℝ)/42188800)-4 = (19760463:ℝ)/42188800 by norm_num]
    exact paid_terminal_744
  · change terminalPayment 745 ≤ terminalValue ((point cut hi 1024 745+point cut hi 1024 746)/2)
    have hp : terminalPayment 745 = (262350427225:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 745+point cut hi 1024 746)/2 = (188540813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188540813:ℝ)/42188800) = (1967723:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188540813:ℝ)/42188800)-4 = (19785613:ℝ)/42188800 by norm_num]
    exact paid_terminal_745
  · change terminalPayment 746 ≤ terminalValue ((point cut hi 1024 746+point cut hi 1024 747)/2)
    have hp : terminalPayment 746 = (261551634966:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 746+point cut hi 1024 747)/2 = (188565963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188565963:ℝ)/42188800) = (1966717:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188565963:ℝ)/42188800)-4 = (19810763:ℝ)/42188800 by norm_num]
    exact paid_terminal_746
  · change terminalPayment 747 ≤ terminalValue ((point cut hi 1024 747+point cut hi 1024 748)/2)
    have hp : terminalPayment 747 = (260751933862:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 747+point cut hi 1024 748)/2 = (188591113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188591113:ℝ)/42188800) = (1965711:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188591113:ℝ)/42188800)-4 = (19835913:ℝ)/42188800 by norm_num]
    exact paid_terminal_747
  · change terminalPayment 748 ≤ terminalValue ((point cut hi 1024 748+point cut hi 1024 749)/2)
    have hp : terminalPayment 748 = (259951322734:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 748+point cut hi 1024 749)/2 = (188616263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188616263:ℝ)/42188800) = (1964705:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188616263:ℝ)/42188800)-4 = (19861063:ℝ)/42188800 by norm_num]
    exact paid_terminal_748
  · change terminalPayment 749 ≤ terminalValue ((point cut hi 1024 749+point cut hi 1024 750)/2)
    have hp : terminalPayment 749 = (259149800401:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 749+point cut hi 1024 750)/2 = (188641413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188641413:ℝ)/42188800) = (1963699:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188641413:ℝ)/42188800)-4 = (19886213:ℝ)/42188800 by norm_num]
    exact paid_terminal_749
  · change terminalPayment 750 ≤ terminalValue ((point cut hi 1024 750+point cut hi 1024 751)/2)
    have hp : terminalPayment 750 = (258347365681:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 750+point cut hi 1024 751)/2 = (188666563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188666563:ℝ)/42188800) = (1962693:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188666563:ℝ)/42188800)-4 = (19911363:ℝ)/42188800 by norm_num]
    exact paid_terminal_750
  · change terminalPayment 751 ≤ terminalValue ((point cut hi 1024 751+point cut hi 1024 752)/2)
    have hp : terminalPayment 751 = (257544017387:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 751+point cut hi 1024 752)/2 = (188691713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((188691713:ℝ)/42188800) = (1961687:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((188691713:ℝ)/42188800)-4 = (19936513:ℝ)/42188800 by norm_num]
    exact paid_terminal_751
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_046
