import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints054
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_054 (j : Fin 16) : terminalPayment (16*54+j.val) ≤
    terminalValue ((point cut hi 1024 (16*54+j.val)+point cut hi 1024 (16*54+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 864 ≤ terminalValue ((point cut hi 1024 864+point cut hi 1024 865)/2)
    have hp : terminalPayment 864 = (160573198549:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 864+point cut hi 1024 865)/2 = (191533663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191533663:ℝ)/42188800) = (1848009:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191533663:ℝ)/42188800)-4 = (22778463:ℝ)/42188800 by norm_num]
    exact paid_terminal_864
  · change terminalPayment 865 ≤ terminalValue ((point cut hi 1024 865+point cut hi 1024 866)/2)
    have hp : terminalPayment 865 = (159657377865:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 865+point cut hi 1024 866)/2 = (191558813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191558813:ℝ)/42188800) = (1847003:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191558813:ℝ)/42188800)-4 = (22803613:ℝ)/42188800 by norm_num]
    exact paid_terminal_865
  · change terminalPayment 866 ≤ terminalValue ((point cut hi 1024 866+point cut hi 1024 867)/2)
    have hp : terminalPayment 866 = (158740492359:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 866+point cut hi 1024 867)/2 = (191583963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191583963:ℝ)/42188800) = (1845997:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191583963:ℝ)/42188800)-4 = (22828763:ℝ)/42188800 by norm_num]
    exact paid_terminal_866
  · change terminalPayment 867 ≤ terminalValue ((point cut hi 1024 867+point cut hi 1024 868)/2)
    have hp : terminalPayment 867 = (157822540576:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 867+point cut hi 1024 868)/2 = (191609113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191609113:ℝ)/42188800) = (1844991:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191609113:ℝ)/42188800)-4 = (22853913:ℝ)/42188800 by norm_num]
    exact paid_terminal_867
  · change terminalPayment 868 ≤ terminalValue ((point cut hi 1024 868+point cut hi 1024 869)/2)
    have hp : terminalPayment 868 = (156903521055:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 868+point cut hi 1024 869)/2 = (191634263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191634263:ℝ)/42188800) = (1843985:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191634263:ℝ)/42188800)-4 = (22879063:ℝ)/42188800 by norm_num]
    exact paid_terminal_868
  · change terminalPayment 869 ≤ terminalValue ((point cut hi 1024 869+point cut hi 1024 870)/2)
    have hp : terminalPayment 869 = (155983432336:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 869+point cut hi 1024 870)/2 = (1860771:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((1860771:ℝ)/409600) = (17893:ℝ)/16384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((1860771:ℝ)/409600)-4 = (222371:ℝ)/409600 by norm_num]
    exact paid_terminal_869
  · change terminalPayment 870 ≤ terminalValue ((point cut hi 1024 870+point cut hi 1024 871)/2)
    have hp : terminalPayment 870 = (155062272954:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 870+point cut hi 1024 871)/2 = (191684563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191684563:ℝ)/42188800) = (1841973:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191684563:ℝ)/42188800)-4 = (22929363:ℝ)/42188800 by norm_num]
    exact paid_terminal_870
  · change terminalPayment 871 ≤ terminalValue ((point cut hi 1024 871+point cut hi 1024 872)/2)
    have hp : terminalPayment 871 = (154140041442:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 871+point cut hi 1024 872)/2 = (191709713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191709713:ℝ)/42188800) = (1840967:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191709713:ℝ)/42188800)-4 = (22954513:ℝ)/42188800 by norm_num]
    exact paid_terminal_871
  · change terminalPayment 872 ≤ terminalValue ((point cut hi 1024 872+point cut hi 1024 873)/2)
    have hp : terminalPayment 872 = (153216736330:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 872+point cut hi 1024 873)/2 = (191734863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191734863:ℝ)/42188800) = (1839961:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191734863:ℝ)/42188800)-4 = (22979663:ℝ)/42188800 by norm_num]
    exact paid_terminal_872
  · change terminalPayment 873 ≤ terminalValue ((point cut hi 1024 873+point cut hi 1024 874)/2)
    have hp : terminalPayment 873 = (152292356146:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 873+point cut hi 1024 874)/2 = (191760013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191760013:ℝ)/42188800) = (1838955:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191760013:ℝ)/42188800)-4 = (23004813:ℝ)/42188800 by norm_num]
    exact paid_terminal_873
  · change terminalPayment 874 ≤ terminalValue ((point cut hi 1024 874+point cut hi 1024 875)/2)
    have hp : terminalPayment 874 = (151366899415:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 874+point cut hi 1024 875)/2 = (191785163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191785163:ℝ)/42188800) = (1837949:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191785163:ℝ)/42188800)-4 = (23029963:ℝ)/42188800 by norm_num]
    exact paid_terminal_874
  · change terminalPayment 875 ≤ terminalValue ((point cut hi 1024 875+point cut hi 1024 876)/2)
    have hp : terminalPayment 875 = (150440364659:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 875+point cut hi 1024 876)/2 = (191810313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191810313:ℝ)/42188800) = (1836943:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191810313:ℝ)/42188800)-4 = (23055113:ℝ)/42188800 by norm_num]
    exact paid_terminal_875
  · change terminalPayment 876 ≤ terminalValue ((point cut hi 1024 876+point cut hi 1024 877)/2)
    have hp : terminalPayment 876 = (149512750398:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 876+point cut hi 1024 877)/2 = (191835463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191835463:ℝ)/42188800) = (1835937:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191835463:ℝ)/42188800)-4 = (23080263:ℝ)/42188800 by norm_num]
    exact paid_terminal_876
  · change terminalPayment 877 ≤ terminalValue ((point cut hi 1024 877+point cut hi 1024 878)/2)
    have hp : terminalPayment 877 = (148584055149:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 877+point cut hi 1024 878)/2 = (191860613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191860613:ℝ)/42188800) = (1834931:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191860613:ℝ)/42188800)-4 = (23105413:ℝ)/42188800 by norm_num]
    exact paid_terminal_877
  · change terminalPayment 878 ≤ terminalValue ((point cut hi 1024 878+point cut hi 1024 879)/2)
    have hp : terminalPayment 878 = (147654277425:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 878+point cut hi 1024 879)/2 = (191885763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191885763:ℝ)/42188800) = (1833925:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191885763:ℝ)/42188800)-4 = (23130563:ℝ)/42188800 by norm_num]
    exact paid_terminal_878
  · change terminalPayment 879 ≤ terminalValue ((point cut hi 1024 879+point cut hi 1024 880)/2)
    have hp : terminalPayment 879 = (146723415739:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 879+point cut hi 1024 880)/2 = (191910913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191910913:ℝ)/42188800) = (1832919:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191910913:ℝ)/42188800)-4 = (23155713:ℝ)/42188800 by norm_num]
    exact paid_terminal_879
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_054
