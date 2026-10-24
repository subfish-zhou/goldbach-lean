import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints056
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_056 (j : Fin 16) : terminalPayment (16*56+j.val) ≤
    terminalValue ((point cut hi 1024 (16*56+j.val)+point cut hi 1024 (16*56+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 896 ≤ terminalValue ((point cut hi 1024 896+point cut hi 1024 897)/2)
    have hp : terminalPayment 896 = (130731465192:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 896+point cut hi 1024 897)/2 = (192338463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192338463:ℝ)/42188800) = (1815817:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192338463:ℝ)/42188800)-4 = (23583263:ℝ)/42188800 by norm_num]
    exact paid_terminal_896
  · change terminalPayment 897 ≤ terminalValue ((point cut hi 1024 897+point cut hi 1024 898)/2)
    have hp : terminalPayment 897 = (129780834523:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 897+point cut hi 1024 898)/2 = (192363613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192363613:ℝ)/42188800) = (1814811:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192363613:ℝ)/42188800)-4 = (23608413:ℝ)/42188800 by norm_num]
    exact paid_terminal_897
  · change terminalPayment 898 ≤ terminalValue ((point cut hi 1024 898+point cut hi 1024 899)/2)
    have hp : terminalPayment 898 = (128829091089:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 898+point cut hi 1024 899)/2 = (192388763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192388763:ℝ)/42188800) = (1813805:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192388763:ℝ)/42188800)-4 = (23633563:ℝ)/42188800 by norm_num]
    exact paid_terminal_898
  · change terminalPayment 899 ≤ terminalValue ((point cut hi 1024 899+point cut hi 1024 900)/2)
    have hp : terminalPayment 899 = (127876233344:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 899+point cut hi 1024 900)/2 = (192413913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192413913:ℝ)/42188800) = (1812799:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192413913:ℝ)/42188800)-4 = (23658713:ℝ)/42188800 by norm_num]
    exact paid_terminal_899
  · change terminalPayment 900 ≤ terminalValue ((point cut hi 1024 900+point cut hi 1024 901)/2)
    have hp : terminalPayment 900 = (126922259742:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 900+point cut hi 1024 901)/2 = (192439063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192439063:ℝ)/42188800) = (1811793:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192439063:ℝ)/42188800)-4 = (23683863:ℝ)/42188800 by norm_num]
    exact paid_terminal_900
  · change terminalPayment 901 ≤ terminalValue ((point cut hi 1024 901+point cut hi 1024 902)/2)
    have hp : terminalPayment 901 = (125967168734:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 901+point cut hi 1024 902)/2 = (192464213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192464213:ℝ)/42188800) = (1810787:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192464213:ℝ)/42188800)-4 = (23709013:ℝ)/42188800 by norm_num]
    exact paid_terminal_901
  · change terminalPayment 902 ≤ terminalValue ((point cut hi 1024 902+point cut hi 1024 903)/2)
    have hp : terminalPayment 902 = (125010958768:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 902+point cut hi 1024 903)/2 = (192489363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192489363:ℝ)/42188800) = (1809781:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192489363:ℝ)/42188800)-4 = (23734163:ℝ)/42188800 by norm_num]
    exact paid_terminal_902
  · change terminalPayment 903 ≤ terminalValue ((point cut hi 1024 903+point cut hi 1024 904)/2)
    have hp : terminalPayment 903 = (124053628287:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 903+point cut hi 1024 904)/2 = (192514513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192514513:ℝ)/42188800) = (1808775:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192514513:ℝ)/42188800)-4 = (23759313:ℝ)/42188800 by norm_num]
    exact paid_terminal_903
  · change terminalPayment 904 ≤ terminalValue ((point cut hi 1024 904+point cut hi 1024 905)/2)
    have hp : terminalPayment 904 = (123095175735:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 904+point cut hi 1024 905)/2 = (192539663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192539663:ℝ)/42188800) = (1807769:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192539663:ℝ)/42188800)-4 = (23784463:ℝ)/42188800 by norm_num]
    exact paid_terminal_904
  · change terminalPayment 905 ≤ terminalValue ((point cut hi 1024 905+point cut hi 1024 906)/2)
    have hp : terminalPayment 905 = (122135599549:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 905+point cut hi 1024 906)/2 = (192564813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192564813:ℝ)/42188800) = (1806763:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192564813:ℝ)/42188800)-4 = (23809613:ℝ)/42188800 by norm_num]
    exact paid_terminal_905
  · change terminalPayment 906 ≤ terminalValue ((point cut hi 1024 906+point cut hi 1024 907)/2)
    have hp : terminalPayment 906 = (121174898167:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 906+point cut hi 1024 907)/2 = (192589963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192589963:ℝ)/42188800) = (1805757:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192589963:ℝ)/42188800)-4 = (23834763:ℝ)/42188800 by norm_num]
    exact paid_terminal_906
  · change terminalPayment 907 ≤ terminalValue ((point cut hi 1024 907+point cut hi 1024 908)/2)
    have hp : terminalPayment 907 = (120213070021:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 907+point cut hi 1024 908)/2 = (192615113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192615113:ℝ)/42188800) = (1804751:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192615113:ℝ)/42188800)-4 = (23859913:ℝ)/42188800 by norm_num]
    exact paid_terminal_907
  · change terminalPayment 908 ≤ terminalValue ((point cut hi 1024 908+point cut hi 1024 909)/2)
    have hp : terminalPayment 908 = (119250113542:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 908+point cut hi 1024 909)/2 = (192640263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192640263:ℝ)/42188800) = (1803745:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192640263:ℝ)/42188800)-4 = (23885063:ℝ)/42188800 by norm_num]
    exact paid_terminal_908
  · change terminalPayment 909 ≤ terminalValue ((point cut hi 1024 909+point cut hi 1024 910)/2)
    have hp : terminalPayment 909 = (118286027158:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 909+point cut hi 1024 910)/2 = (192665413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192665413:ℝ)/42188800) = (1802739:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192665413:ℝ)/42188800)-4 = (23910213:ℝ)/42188800 by norm_num]
    exact paid_terminal_909
  · change terminalPayment 910 ≤ terminalValue ((point cut hi 1024 910+point cut hi 1024 911)/2)
    have hp : terminalPayment 910 = (117320809293:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 910+point cut hi 1024 911)/2 = (192690563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192690563:ℝ)/42188800) = (1801733:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192690563:ℝ)/42188800)-4 = (23935363:ℝ)/42188800 by norm_num]
    exact paid_terminal_910
  · change terminalPayment 911 ≤ terminalValue ((point cut hi 1024 911+point cut hi 1024 912)/2)
    have hp : terminalPayment 911 = (116354458368:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 911+point cut hi 1024 912)/2 = (192715713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((192715713:ℝ)/42188800) = (1800727:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((192715713:ℝ)/42188800)-4 = (23960513:ℝ)/42188800 by norm_num]
    exact paid_terminal_911
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_056
