import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints050
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_050 (j : Fin 16) : terminalPayment (16*50+j.val) ≤
    terminalValue ((point cut hi 1024 (16*50+j.val)+point cut hi 1024 (16*50+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 800 ≤ terminalValue ((point cut hi 1024 800+point cut hi 1024 801)/2)
    have hp : terminalPayment 800 = (217035573215:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 800+point cut hi 1024 801)/2 = (189924063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189924063:ℝ)/42188800) = (1912393:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189924063:ℝ)/42188800)-4 = (21168863:ℝ)/42188800 by norm_num]
    exact paid_terminal_800
  · change terminalPayment 801 ≤ terminalValue ((point cut hi 1024 801+point cut hi 1024 802)/2)
    have hp : terminalPayment 801 = (216184988372:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 801+point cut hi 1024 802)/2 = (189949213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189949213:ℝ)/42188800) = (1911387:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189949213:ℝ)/42188800)-4 = (21194013:ℝ)/42188800 by norm_num]
    exact paid_terminal_801
  · change terminalPayment 802 ≤ terminalValue ((point cut hi 1024 802+point cut hi 1024 803)/2)
    have hp : terminalPayment 802 = (215333426676:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 802+point cut hi 1024 803)/2 = (189974363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189974363:ℝ)/42188800) = (1910381:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189974363:ℝ)/42188800)-4 = (21219163:ℝ)/42188800 by norm_num]
    exact paid_terminal_802
  · change terminalPayment 803 ≤ terminalValue ((point cut hi 1024 803+point cut hi 1024 804)/2)
    have hp : terminalPayment 803 = (214480886827:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 803+point cut hi 1024 804)/2 = (189999513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((189999513:ℝ)/42188800) = (1909375:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((189999513:ℝ)/42188800)-4 = (21244313:ℝ)/42188800 by norm_num]
    exact paid_terminal_803
  · change terminalPayment 804 ≤ terminalValue ((point cut hi 1024 804+point cut hi 1024 805)/2)
    have hp : terminalPayment 804 = (213627367525:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 804+point cut hi 1024 805)/2 = (190024663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190024663:ℝ)/42188800) = (1908369:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190024663:ℝ)/42188800)-4 = (21269463:ℝ)/42188800 by norm_num]
    exact paid_terminal_804
  · change terminalPayment 805 ≤ terminalValue ((point cut hi 1024 805+point cut hi 1024 806)/2)
    have hp : terminalPayment 805 = (212772867466:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 805+point cut hi 1024 806)/2 = (190049813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190049813:ℝ)/42188800) = (1907363:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190049813:ℝ)/42188800)-4 = (21294613:ℝ)/42188800 by norm_num]
    exact paid_terminal_805
  · change terminalPayment 806 ≤ terminalValue ((point cut hi 1024 806+point cut hi 1024 807)/2)
    have hp : terminalPayment 806 = (211917385345:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 806+point cut hi 1024 807)/2 = (190074963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190074963:ℝ)/42188800) = (1906357:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190074963:ℝ)/42188800)-4 = (21319763:ℝ)/42188800 by norm_num]
    exact paid_terminal_806
  · change terminalPayment 807 ≤ terminalValue ((point cut hi 1024 807+point cut hi 1024 808)/2)
    have hp : terminalPayment 807 = (211060919855:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 807+point cut hi 1024 808)/2 = (190100113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190100113:ℝ)/42188800) = (1905351:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190100113:ℝ)/42188800)-4 = (21344913:ℝ)/42188800 by norm_num]
    exact paid_terminal_807
  · change terminalPayment 808 ≤ terminalValue ((point cut hi 1024 808+point cut hi 1024 809)/2)
    have hp : terminalPayment 808 = (210203469684:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 808+point cut hi 1024 809)/2 = (190125263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190125263:ℝ)/42188800) = (1904345:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190125263:ℝ)/42188800)-4 = (21370063:ℝ)/42188800 by norm_num]
    exact paid_terminal_808
  · change terminalPayment 809 ≤ terminalValue ((point cut hi 1024 809+point cut hi 1024 810)/2)
    have hp : terminalPayment 809 = (209345033521:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 809+point cut hi 1024 810)/2 = (190150413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190150413:ℝ)/42188800) = (1903339:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190150413:ℝ)/42188800)-4 = (21395213:ℝ)/42188800 by norm_num]
    exact paid_terminal_809
  · change terminalPayment 810 ≤ terminalValue ((point cut hi 1024 810+point cut hi 1024 811)/2)
    have hp : terminalPayment 810 = (208485610050:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 810+point cut hi 1024 811)/2 = (190175563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190175563:ℝ)/42188800) = (1902333:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190175563:ℝ)/42188800)-4 = (21420363:ℝ)/42188800 by norm_num]
    exact paid_terminal_810
  · change terminalPayment 811 ≤ terminalValue ((point cut hi 1024 811+point cut hi 1024 812)/2)
    have hp : terminalPayment 811 = (207625197955:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 811+point cut hi 1024 812)/2 = (190200713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190200713:ℝ)/42188800) = (1901327:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190200713:ℝ)/42188800)-4 = (21445513:ℝ)/42188800 by norm_num]
    exact paid_terminal_811
  · change terminalPayment 812 ≤ terminalValue ((point cut hi 1024 812+point cut hi 1024 813)/2)
    have hp : terminalPayment 812 = (206763795916:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 812+point cut hi 1024 813)/2 = (190225863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190225863:ℝ)/42188800) = (1900321:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190225863:ℝ)/42188800)-4 = (21470663:ℝ)/42188800 by norm_num]
    exact paid_terminal_812
  · change terminalPayment 813 ≤ terminalValue ((point cut hi 1024 813+point cut hi 1024 814)/2)
    have hp : terminalPayment 813 = (205901402611:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 813+point cut hi 1024 814)/2 = (190251013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190251013:ℝ)/42188800) = (1899315:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190251013:ℝ)/42188800)-4 = (21495813:ℝ)/42188800 by norm_num]
    exact paid_terminal_813
  · change terminalPayment 814 ≤ terminalValue ((point cut hi 1024 814+point cut hi 1024 815)/2)
    have hp : terminalPayment 814 = (205038016715:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 814+point cut hi 1024 815)/2 = (190276163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190276163:ℝ)/42188800) = (1898309:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190276163:ℝ)/42188800)-4 = (21520963:ℝ)/42188800 by norm_num]
    exact paid_terminal_814
  · change terminalPayment 815 ≤ terminalValue ((point cut hi 1024 815+point cut hi 1024 816)/2)
    have hp : terminalPayment 815 = (204173636903:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 815+point cut hi 1024 816)/2 = (190301313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((190301313:ℝ)/42188800) = (1897303:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((190301313:ℝ)/42188800)-4 = (21546113:ℝ)/42188800 by norm_num]
    exact paid_terminal_815
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_050
