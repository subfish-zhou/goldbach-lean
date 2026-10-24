import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints003
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_003 (j : Fin 16) : terminalPayment (16*3+j.val) ≤
    terminalValue ((point cut hi 1024 (16*3+j.val)+point cut hi 1024 (16*3+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 48 ≤ terminalValue ((point cut hi 1024 48+point cut hi 1024 49)/2)
    have hp : terminalPayment 48 = (648898088223:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 48+point cut hi 1024 49)/2 = (171011263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171011263:ℝ)/42188800) = (2668905:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171011263:ℝ)/42188800)-4 = (2256063:ℝ)/42188800 by norm_num]
    exact paid_terminal_48
  · change terminalPayment 49 ≤ terminalValue ((point cut hi 1024 49+point cut hi 1024 50)/2)
    have hp : terminalPayment 49 = (648532265692:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 49+point cut hi 1024 50)/2 = (171036413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171036413:ℝ)/42188800) = (2667899:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171036413:ℝ)/42188800)-4 = (2281213:ℝ)/42188800 by norm_num]
    exact paid_terminal_49
  · change terminalPayment 50 ≤ terminalValue ((point cut hi 1024 50+point cut hi 1024 51)/2)
    have hp : terminalPayment 50 = (648166017203:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 50+point cut hi 1024 51)/2 = (171061563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171061563:ℝ)/42188800) = (2666893:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171061563:ℝ)/42188800)-4 = (2306363:ℝ)/42188800 by norm_num]
    exact paid_terminal_50
  · change terminalPayment 51 ≤ terminalValue ((point cut hi 1024 51+point cut hi 1024 52)/2)
    have hp : terminalPayment 51 = (647799342393:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 51+point cut hi 1024 52)/2 = (171086713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171086713:ℝ)/42188800) = (2665887:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171086713:ℝ)/42188800)-4 = (2331513:ℝ)/42188800 by norm_num]
    exact paid_terminal_51
  · change terminalPayment 52 ≤ terminalValue ((point cut hi 1024 52+point cut hi 1024 53)/2)
    have hp : terminalPayment 52 = (647432240897:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 52+point cut hi 1024 53)/2 = (171111863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171111863:ℝ)/42188800) = (2664881:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171111863:ℝ)/42188800)-4 = (2356663:ℝ)/42188800 by norm_num]
    exact paid_terminal_52
  · change terminalPayment 53 ≤ terminalValue ((point cut hi 1024 53+point cut hi 1024 54)/2)
    have hp : terminalPayment 53 = (647064712352:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 53+point cut hi 1024 54)/2 = (171137013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171137013:ℝ)/42188800) = (2663875:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171137013:ℝ)/42188800)-4 = (2381813:ℝ)/42188800 by norm_num]
    exact paid_terminal_53
  · change terminalPayment 54 ≤ terminalValue ((point cut hi 1024 54+point cut hi 1024 55)/2)
    have hp : terminalPayment 54 = (646696756392:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 54+point cut hi 1024 55)/2 = (171162163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171162163:ℝ)/42188800) = (2662869:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171162163:ℝ)/42188800)-4 = (2406963:ℝ)/42188800 by norm_num]
    exact paid_terminal_54
  · change terminalPayment 55 ≤ terminalValue ((point cut hi 1024 55+point cut hi 1024 56)/2)
    have hp : terminalPayment 55 = (646328372651:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 55+point cut hi 1024 56)/2 = (171187313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171187313:ℝ)/42188800) = (2661863:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171187313:ℝ)/42188800)-4 = (2432113:ℝ)/42188800 by norm_num]
    exact paid_terminal_55
  · change terminalPayment 56 ≤ terminalValue ((point cut hi 1024 56+point cut hi 1024 57)/2)
    have hp : terminalPayment 56 = (645959560763:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 56+point cut hi 1024 57)/2 = (171212463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171212463:ℝ)/42188800) = (2660857:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171212463:ℝ)/42188800)-4 = (2457263:ℝ)/42188800 by norm_num]
    exact paid_terminal_56
  · change terminalPayment 57 ≤ terminalValue ((point cut hi 1024 57+point cut hi 1024 58)/2)
    have hp : terminalPayment 57 = (645590320361:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 57+point cut hi 1024 58)/2 = (171237613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171237613:ℝ)/42188800) = (2659851:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171237613:ℝ)/42188800)-4 = (2482413:ℝ)/42188800 by norm_num]
    exact paid_terminal_57
  · change terminalPayment 58 ≤ terminalValue ((point cut hi 1024 58+point cut hi 1024 59)/2)
    have hp : terminalPayment 58 = (645220651076:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 58+point cut hi 1024 59)/2 = (171262763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171262763:ℝ)/42188800) = (2658845:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171262763:ℝ)/42188800)-4 = (2507563:ℝ)/42188800 by norm_num]
    exact paid_terminal_58
  · change terminalPayment 59 ≤ terminalValue ((point cut hi 1024 59+point cut hi 1024 60)/2)
    have hp : terminalPayment 59 = (644850552542:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 59+point cut hi 1024 60)/2 = (171287913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171287913:ℝ)/42188800) = (2657839:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171287913:ℝ)/42188800)-4 = (2532713:ℝ)/42188800 by norm_num]
    exact paid_terminal_59
  · change terminalPayment 60 ≤ terminalValue ((point cut hi 1024 60+point cut hi 1024 61)/2)
    have hp : terminalPayment 60 = (644480024387:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 60+point cut hi 1024 61)/2 = (171313063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171313063:ℝ)/42188800) = (2656833:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171313063:ℝ)/42188800)-4 = (2557863:ℝ)/42188800 by norm_num]
    exact paid_terminal_60
  · change terminalPayment 61 ≤ terminalValue ((point cut hi 1024 61+point cut hi 1024 62)/2)
    have hp : terminalPayment 61 = (644109066243:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 61+point cut hi 1024 62)/2 = (171338213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171338213:ℝ)/42188800) = (2655827:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171338213:ℝ)/42188800)-4 = (2583013:ℝ)/42188800 by norm_num]
    exact paid_terminal_61
  · change terminalPayment 62 ≤ terminalValue ((point cut hi 1024 62+point cut hi 1024 63)/2)
    have hp : terminalPayment 62 = (643737677739:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 62+point cut hi 1024 63)/2 = (171363363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171363363:ℝ)/42188800) = (2654821:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171363363:ℝ)/42188800)-4 = (2608163:ℝ)/42188800 by norm_num]
    exact paid_terminal_62
  · change terminalPayment 63 ≤ terminalValue ((point cut hi 1024 63+point cut hi 1024 64)/2)
    have hp : terminalPayment 63 = (643365858504:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 63+point cut hi 1024 64)/2 = (171388513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((171388513:ℝ)/42188800) = (2653815:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((171388513:ℝ)/42188800)-4 = (2633313:ℝ)/42188800 by norm_num]
    exact paid_terminal_63
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_003
