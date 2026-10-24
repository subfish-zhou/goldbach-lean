import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints044
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_044 (j : Fin 16) : terminalPayment (16*44+j.val) ≤
    terminalValue ((point cut hi 1024 (16*44+j.val)+point cut hi 1024 (16*44+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 704 ≤ terminalValue ((point cut hi 1024 704+point cut hi 1024 705)/2)
    have hp : terminalPayment 704 = (294332668247:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 704+point cut hi 1024 705)/2 = (187509663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187509663:ℝ)/42188800) = (2008969:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187509663:ℝ)/42188800)-4 = (18754463:ℝ)/42188800 by norm_num]
    exact paid_terminal_704
  · change terminalPayment 705 ≤ terminalValue ((point cut hi 1024 705+point cut hi 1024 706)/2)
    have hp : terminalPayment 705 = (293570148475:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 705+point cut hi 1024 706)/2 = (187534813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187534813:ℝ)/42188800) = (2007963:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187534813:ℝ)/42188800)-4 = (18779613:ℝ)/42188800 by norm_num]
    exact paid_terminal_705
  · change terminalPayment 706 ≤ terminalValue ((point cut hi 1024 706+point cut hi 1024 707)/2)
    have hp : terminalPayment 706 = (292806766471:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 706+point cut hi 1024 707)/2 = (187559963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187559963:ℝ)/42188800) = (2006957:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187559963:ℝ)/42188800)-4 = (18804763:ℝ)/42188800 by norm_num]
    exact paid_terminal_706
  · change terminalPayment 707 ≤ terminalValue ((point cut hi 1024 707+point cut hi 1024 708)/2)
    have hp : terminalPayment 707 = (292042521135:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 707+point cut hi 1024 708)/2 = (187585113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187585113:ℝ)/42188800) = (2005951:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187585113:ℝ)/42188800)-4 = (18829913:ℝ)/42188800 by norm_num]
    exact paid_terminal_707
  · change terminalPayment 708 ≤ terminalValue ((point cut hi 1024 708+point cut hi 1024 709)/2)
    have hp : terminalPayment 708 = (291277411367:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 708+point cut hi 1024 709)/2 = (187610263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187610263:ℝ)/42188800) = (2004945:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187610263:ℝ)/42188800)-4 = (18855063:ℝ)/42188800 by norm_num]
    exact paid_terminal_708
  · change terminalPayment 709 ≤ terminalValue ((point cut hi 1024 709+point cut hi 1024 710)/2)
    have hp : terminalPayment 709 = (290511436067:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 709+point cut hi 1024 710)/2 = (187635413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187635413:ℝ)/42188800) = (2003939:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187635413:ℝ)/42188800)-4 = (18880213:ℝ)/42188800 by norm_num]
    exact paid_terminal_709
  · change terminalPayment 710 ≤ terminalValue ((point cut hi 1024 710+point cut hi 1024 711)/2)
    have hp : terminalPayment 710 = (289744594130:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 710+point cut hi 1024 711)/2 = (187660563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187660563:ℝ)/42188800) = (2002933:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187660563:ℝ)/42188800)-4 = (18905363:ℝ)/42188800 by norm_num]
    exact paid_terminal_710
  · change terminalPayment 711 ≤ terminalValue ((point cut hi 1024 711+point cut hi 1024 712)/2)
    have hp : terminalPayment 711 = (288976884451:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 711+point cut hi 1024 712)/2 = (187685713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187685713:ℝ)/42188800) = (2001927:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187685713:ℝ)/42188800)-4 = (18930513:ℝ)/42188800 by norm_num]
    exact paid_terminal_711
  · change terminalPayment 712 ≤ terminalValue ((point cut hi 1024 712+point cut hi 1024 713)/2)
    have hp : terminalPayment 712 = (288208305923:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 712+point cut hi 1024 713)/2 = (187710863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187710863:ℝ)/42188800) = (2000921:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187710863:ℝ)/42188800)-4 = (18955663:ℝ)/42188800 by norm_num]
    exact paid_terminal_712
  · change terminalPayment 713 ≤ terminalValue ((point cut hi 1024 713+point cut hi 1024 714)/2)
    have hp : terminalPayment 713 = (287438857435:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 713+point cut hi 1024 714)/2 = (187736013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187736013:ℝ)/42188800) = (1999915:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187736013:ℝ)/42188800)-4 = (18980813:ℝ)/42188800 by norm_num]
    exact paid_terminal_713
  · change terminalPayment 714 ≤ terminalValue ((point cut hi 1024 714+point cut hi 1024 715)/2)
    have hp : terminalPayment 714 = (286668537877:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 714+point cut hi 1024 715)/2 = (187761163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187761163:ℝ)/42188800) = (1998909:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187761163:ℝ)/42188800)-4 = (19005963:ℝ)/42188800 by norm_num]
    exact paid_terminal_714
  · change terminalPayment 715 ≤ terminalValue ((point cut hi 1024 715+point cut hi 1024 716)/2)
    have hp : terminalPayment 715 = (285897346136:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 715+point cut hi 1024 716)/2 = (187786313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187786313:ℝ)/42188800) = (1997903:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187786313:ℝ)/42188800)-4 = (19031113:ℝ)/42188800 by norm_num]
    exact paid_terminal_715
  · change terminalPayment 716 ≤ terminalValue ((point cut hi 1024 716+point cut hi 1024 717)/2)
    have hp : terminalPayment 716 = (285125281096:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 716+point cut hi 1024 717)/2 = (187811463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187811463:ℝ)/42188800) = (1996897:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187811463:ℝ)/42188800)-4 = (19056263:ℝ)/42188800 by norm_num]
    exact paid_terminal_716
  · change terminalPayment 717 ≤ terminalValue ((point cut hi 1024 717+point cut hi 1024 718)/2)
    have hp : terminalPayment 717 = (284352341640:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 717+point cut hi 1024 718)/2 = (187836613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187836613:ℝ)/42188800) = (1995891:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187836613:ℝ)/42188800)-4 = (19081413:ℝ)/42188800 by norm_num]
    exact paid_terminal_717
  · change terminalPayment 718 ≤ terminalValue ((point cut hi 1024 718+point cut hi 1024 719)/2)
    have hp : terminalPayment 718 = (283578526650:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 718+point cut hi 1024 719)/2 = (187861763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187861763:ℝ)/42188800) = (1994885:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187861763:ℝ)/42188800)-4 = (19106563:ℝ)/42188800 by norm_num]
    exact paid_terminal_718
  · change terminalPayment 719 ≤ terminalValue ((point cut hi 1024 719+point cut hi 1024 720)/2)
    have hp : terminalPayment 719 = (282803835003:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 719+point cut hi 1024 720)/2 = (187886913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((187886913:ℝ)/42188800) = (1993879:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((187886913:ℝ)/42188800)-4 = (19131713:ℝ)/42188800 by norm_num]
    exact paid_terminal_719
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_044
