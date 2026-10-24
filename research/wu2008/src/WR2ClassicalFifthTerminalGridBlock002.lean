import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints002
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_002 (j : Fin 16) : terminalPayment (16*2+j.val) ≤
    terminalValue ((point cut hi 1024 (16*2+j.val)+point cut hi 1024 (16*2+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 32 ≤ terminalValue ((point cut hi 1024 32+point cut hi 1024 33)/2)
    have hp : terminalPayment 32 = (654693612221:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 32+point cut hi 1024 33)/2 = (170608863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170608863:ℝ)/42188800) = (2685001:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170608863:ℝ)/42188800)-4 = (1853663:ℝ)/42188800 by norm_num]
    exact paid_terminal_32
  · change terminalPayment 33 ≤ terminalValue ((point cut hi 1024 33+point cut hi 1024 34)/2)
    have hp : terminalPayment 33 = (654334556162:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 33+point cut hi 1024 34)/2 = (170634013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170634013:ℝ)/42188800) = (2683995:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170634013:ℝ)/42188800)-4 = (1878813:ℝ)/42188800 by norm_num]
    exact paid_terminal_33
  · change terminalPayment 34 ≤ terminalValue ((point cut hi 1024 34+point cut hi 1024 35)/2)
    have hp : terminalPayment 34 = (653975079868:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 34+point cut hi 1024 35)/2 = (170659163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170659163:ℝ)/42188800) = (2682989:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170659163:ℝ)/42188800)-4 = (1903963:ℝ)/42188800 by norm_num]
    exact paid_terminal_34
  · change terminalPayment 35 ≤ terminalValue ((point cut hi 1024 35+point cut hi 1024 36)/2)
    have hp : terminalPayment 35 = (653615182984:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 35+point cut hi 1024 36)/2 = (170684313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170684313:ℝ)/42188800) = (2681983:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170684313:ℝ)/42188800)-4 = (1929113:ℝ)/42188800 by norm_num]
    exact paid_terminal_35
  · change terminalPayment 36 ≤ terminalValue ((point cut hi 1024 36+point cut hi 1024 37)/2)
    have hp : terminalPayment 36 = (653254865158:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 36+point cut hi 1024 37)/2 = (170709463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170709463:ℝ)/42188800) = (2680977:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170709463:ℝ)/42188800)-4 = (1954263:ℝ)/42188800 by norm_num]
    exact paid_terminal_36
  · change terminalPayment 37 ≤ terminalValue ((point cut hi 1024 37+point cut hi 1024 38)/2)
    have hp : terminalPayment 37 = (652894126036:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 37+point cut hi 1024 38)/2 = (170734613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170734613:ℝ)/42188800) = (2679971:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170734613:ℝ)/42188800)-4 = (1979413:ℝ)/42188800 by norm_num]
    exact paid_terminal_37
  · change terminalPayment 38 ≤ terminalValue ((point cut hi 1024 38+point cut hi 1024 39)/2)
    have hp : terminalPayment 38 = (652532965263:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 38+point cut hi 1024 39)/2 = (170759763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170759763:ℝ)/42188800) = (2678965:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170759763:ℝ)/42188800)-4 = (2004563:ℝ)/42188800 by norm_num]
    exact paid_terminal_38
  · change terminalPayment 39 ≤ terminalValue ((point cut hi 1024 39+point cut hi 1024 40)/2)
    have hp : terminalPayment 39 = (652171382483:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 39+point cut hi 1024 40)/2 = (170784913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170784913:ℝ)/42188800) = (2677959:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170784913:ℝ)/42188800)-4 = (2029713:ℝ)/42188800 by norm_num]
    exact paid_terminal_39
  · change terminalPayment 40 ≤ terminalValue ((point cut hi 1024 40+point cut hi 1024 41)/2)
    have hp : terminalPayment 40 = (651809377341:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 40+point cut hi 1024 41)/2 = (170810063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170810063:ℝ)/42188800) = (2676953:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170810063:ℝ)/42188800)-4 = (2054863:ℝ)/42188800 by norm_num]
    exact paid_terminal_40
  · change terminalPayment 41 ≤ terminalValue ((point cut hi 1024 41+point cut hi 1024 42)/2)
    have hp : terminalPayment 41 = (651446949479:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 41+point cut hi 1024 42)/2 = (170835213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170835213:ℝ)/42188800) = (2675947:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170835213:ℝ)/42188800)-4 = (2080013:ℝ)/42188800 by norm_num]
    exact paid_terminal_41
  · change terminalPayment 42 ≤ terminalValue ((point cut hi 1024 42+point cut hi 1024 43)/2)
    have hp : terminalPayment 42 = (651084098542:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 42+point cut hi 1024 43)/2 = (170860363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170860363:ℝ)/42188800) = (2674941:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170860363:ℝ)/42188800)-4 = (2105163:ℝ)/42188800 by norm_num]
    exact paid_terminal_42
  · change terminalPayment 43 ≤ terminalValue ((point cut hi 1024 43+point cut hi 1024 44)/2)
    have hp : terminalPayment 43 = (650720824170:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 43+point cut hi 1024 44)/2 = (170885513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170885513:ℝ)/42188800) = (2673935:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170885513:ℝ)/42188800)-4 = (2130313:ℝ)/42188800 by norm_num]
    exact paid_terminal_43
  · change terminalPayment 44 ≤ terminalValue ((point cut hi 1024 44+point cut hi 1024 45)/2)
    have hp : terminalPayment 44 = (650357126005:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 44+point cut hi 1024 45)/2 = (170910663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170910663:ℝ)/42188800) = (2672929:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170910663:ℝ)/42188800)-4 = (2155463:ℝ)/42188800 by norm_num]
    exact paid_terminal_44
  · change terminalPayment 45 ≤ terminalValue ((point cut hi 1024 45+point cut hi 1024 46)/2)
    have hp : terminalPayment 45 = (649993003688:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 45+point cut hi 1024 46)/2 = (1659571:ℝ)/409600 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((1659571:ℝ)/409600) = (25941:ℝ)/16384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((1659571:ℝ)/409600)-4 = (21171:ℝ)/409600 by norm_num]
    exact paid_terminal_45
  · change terminalPayment 46 ≤ terminalValue ((point cut hi 1024 46+point cut hi 1024 47)/2)
    have hp : terminalPayment 46 = (649628456859:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 46+point cut hi 1024 47)/2 = (170960963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170960963:ℝ)/42188800) = (2670917:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170960963:ℝ)/42188800)-4 = (2205763:ℝ)/42188800 by norm_num]
    exact paid_terminal_46
  · change terminalPayment 47 ≤ terminalValue ((point cut hi 1024 47+point cut hi 1024 48)/2)
    have hp : terminalPayment 47 = (649263485158:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 47+point cut hi 1024 48)/2 = (170986113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((170986113:ℝ)/42188800) = (2669911:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((170986113:ℝ)/42188800)-4 = (2230913:ℝ)/42188800 by norm_num]
    exact paid_terminal_47
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_002
