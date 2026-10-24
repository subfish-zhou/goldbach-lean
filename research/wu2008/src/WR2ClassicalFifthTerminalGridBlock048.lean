import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints048
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_048 (j : Fin 16) : terminalPayment (16*48+j.val) ≤
    terminalValue ((point cut hi 1024 (16*48+j.val)+point cut hi 1024 (16*48+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 768 ≤ terminalValue ((point cut hi 1024 768+point cut hi 1024 769)/2)
    have hp : terminalPayment 768 = (243746161296:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 768+point cut hi 1024 769)/2 = (189119263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189119263:ℝ)/42188800) = (1944585:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189119263:ℝ)/42188800)-4 = (20364063:ℝ)/42188800 by norm_num]
    exact paid_terminal_768
  · change terminalPayment 769 ≤ terminalValue ((point cut hi 1024 769+point cut hi 1024 770)/2)
    have hp : terminalPayment 769 = (242926163660:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 769+point cut hi 1024 770)/2 = (189144413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189144413:ℝ)/42188800) = (1943579:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189144413:ℝ)/42188800)-4 = (20389213:ℝ)/42188800 by norm_num]
    exact paid_terminal_769
  · change terminalPayment 770 ≤ terminalValue ((point cut hi 1024 770+point cut hi 1024 771)/2)
    have hp : terminalPayment 770 = (242105229537:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 770+point cut hi 1024 771)/2 = (189169563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189169563:ℝ)/42188800) = (1942573:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189169563:ℝ)/42188800)-4 = (20414363:ℝ)/42188800 by norm_num]
    exact paid_terminal_770
  · change terminalPayment 771 ≤ terminalValue ((point cut hi 1024 771+point cut hi 1024 772)/2)
    have hp : terminalPayment 771 = (241283357699:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 771+point cut hi 1024 772)/2 = (189194713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189194713:ℝ)/42188800) = (1941567:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189194713:ℝ)/42188800)-4 = (20439513:ℝ)/42188800 by norm_num]
    exact paid_terminal_771
  · change terminalPayment 772 ≤ terminalValue ((point cut hi 1024 772+point cut hi 1024 773)/2)
    have hp : terminalPayment 772 = (240460546917:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 772+point cut hi 1024 773)/2 = (189219863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189219863:ℝ)/42188800) = (1940561:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189219863:ℝ)/42188800)-4 = (20464663:ℝ)/42188800 by norm_num]
    exact paid_terminal_772
  · change terminalPayment 773 ≤ terminalValue ((point cut hi 1024 773+point cut hi 1024 774)/2)
    have hp : terminalPayment 773 = (239636795958:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 773+point cut hi 1024 774)/2 = (189245013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189245013:ℝ)/42188800) = (1939555:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189245013:ℝ)/42188800)-4 = (20489813:ℝ)/42188800 by norm_num]
    exact paid_terminal_773
  · change terminalPayment 774 ≤ terminalValue ((point cut hi 1024 774+point cut hi 1024 775)/2)
    have hp : terminalPayment 774 = (238812103590:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 774+point cut hi 1024 775)/2 = (189270163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189270163:ℝ)/42188800) = (1938549:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189270163:ℝ)/42188800)-4 = (20514963:ℝ)/42188800 by norm_num]
    exact paid_terminal_774
  · change terminalPayment 775 ≤ terminalValue ((point cut hi 1024 775+point cut hi 1024 776)/2)
    have hp : terminalPayment 775 = (237986468577:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 775+point cut hi 1024 776)/2 = (189295313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189295313:ℝ)/42188800) = (1937543:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189295313:ℝ)/42188800)-4 = (20540113:ℝ)/42188800 by norm_num]
    exact paid_terminal_775
  · change terminalPayment 776 ≤ terminalValue ((point cut hi 1024 776+point cut hi 1024 777)/2)
    have hp : terminalPayment 776 = (237159889679:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 776+point cut hi 1024 777)/2 = (189320463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189320463:ℝ)/42188800) = (1936537:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189320463:ℝ)/42188800)-4 = (20565263:ℝ)/42188800 by norm_num]
    exact paid_terminal_776
  · change terminalPayment 777 ≤ terminalValue ((point cut hi 1024 777+point cut hi 1024 778)/2)
    have hp : terminalPayment 777 = (236332365657:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 777+point cut hi 1024 778)/2 = (189345613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189345613:ℝ)/42188800) = (1935531:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189345613:ℝ)/42188800)-4 = (20590413:ℝ)/42188800 by norm_num]
    exact paid_terminal_777
  · change terminalPayment 778 ≤ terminalValue ((point cut hi 1024 778+point cut hi 1024 779)/2)
    have hp : terminalPayment 778 = (235503895269:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 778+point cut hi 1024 779)/2 = (189370763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189370763:ℝ)/42188800) = (1934525:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189370763:ℝ)/42188800)-4 = (20615563:ℝ)/42188800 by norm_num]
    exact paid_terminal_778
  · change terminalPayment 779 ≤ terminalValue ((point cut hi 1024 779+point cut hi 1024 780)/2)
    have hp : terminalPayment 779 = (234674477269:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 779+point cut hi 1024 780)/2 = (189395913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189395913:ℝ)/42188800) = (1933519:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189395913:ℝ)/42188800)-4 = (20640713:ℝ)/42188800 by norm_num]
    exact paid_terminal_779
  · change terminalPayment 780 ≤ terminalValue ((point cut hi 1024 780+point cut hi 1024 781)/2)
    have hp : terminalPayment 780 = (233844110411:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 780+point cut hi 1024 781)/2 = (189421063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189421063:ℝ)/42188800) = (1932513:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189421063:ℝ)/42188800)-4 = (20665863:ℝ)/42188800 by norm_num]
    exact paid_terminal_780
  · change terminalPayment 781 ≤ terminalValue ((point cut hi 1024 781+point cut hi 1024 782)/2)
    have hp : terminalPayment 781 = (233012793446:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 781+point cut hi 1024 782)/2 = (189446213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189446213:ℝ)/42188800) = (1931507:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189446213:ℝ)/42188800)-4 = (20691013:ℝ)/42188800 by norm_num]
    exact paid_terminal_781
  · change terminalPayment 782 ≤ terminalValue ((point cut hi 1024 782+point cut hi 1024 783)/2)
    have hp : terminalPayment 782 = (232180525122:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 782+point cut hi 1024 783)/2 = (189471363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189471363:ℝ)/42188800) = (1930501:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189471363:ℝ)/42188800)-4 = (20716163:ℝ)/42188800 by norm_num]
    exact paid_terminal_782
  · change terminalPayment 783 ≤ terminalValue ((point cut hi 1024 783+point cut hi 1024 784)/2)
    have hp : terminalPayment 783 = (231347304186:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 783+point cut hi 1024 784)/2 = (189496513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189496513:ℝ)/42188800) = (1929495:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189496513:ℝ)/42188800)-4 = (20741313:ℝ)/42188800 by norm_num]
    exact paid_terminal_783
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_048
