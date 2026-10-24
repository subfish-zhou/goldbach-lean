import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints059
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_059 (j : Fin 16) : terminalPayment (16*59+j.val) ≤
    terminalValue ((point cut hi 1024 (16*59+j.val)+point cut hi 1024 (16*59+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 944 ≤ terminalValue ((point cut hi 1024 944+point cut hi 1024 945)/2)
    have hp : terminalPayment 944 = (83818728102:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 944+point cut hi 1024 945)/2 = (193545663:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193545663:ℝ)/42188800) = (1767529:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193545663:ℝ)/42188800)-4 = (24790463:ℝ)/42188800 by norm_num]
    exact paid_terminal_944
  · change terminalPayment 945 ≤ terminalValue ((point cut hi 1024 945+point cut hi 1024 946)/2)
    have hp : terminalPayment 945 = (82812892943:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 945+point cut hi 1024 946)/2 = (193570813:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193570813:ℝ)/42188800) = (1766523:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193570813:ℝ)/42188800)-4 = (24815613:ℝ)/42188800 by norm_num]
    exact paid_terminal_945
  · change terminalPayment 946 ≤ terminalValue ((point cut hi 1024 946+point cut hi 1024 947)/2)
    have hp : terminalPayment 946 = (81805867607:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 946+point cut hi 1024 947)/2 = (193595963:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193595963:ℝ)/42188800) = (1765517:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193595963:ℝ)/42188800)-4 = (24840763:ℝ)/42188800 by norm_num]
    exact paid_terminal_946
  · change terminalPayment 947 ≤ terminalValue ((point cut hi 1024 947+point cut hi 1024 948)/2)
    have hp : terminalPayment 947 = (80797650405:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 947+point cut hi 1024 948)/2 = (193621113:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193621113:ℝ)/42188800) = (1764511:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193621113:ℝ)/42188800)-4 = (24865913:ℝ)/42188800 by norm_num]
    exact paid_terminal_947
  · change terminalPayment 948 ≤ terminalValue ((point cut hi 1024 948+point cut hi 1024 949)/2)
    have hp : terminalPayment 948 = (79788239648:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 948+point cut hi 1024 949)/2 = (193646263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193646263:ℝ)/42188800) = (1763505:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193646263:ℝ)/42188800)-4 = (24891063:ℝ)/42188800 by norm_num]
    exact paid_terminal_948
  · change terminalPayment 949 ≤ terminalValue ((point cut hi 1024 949+point cut hi 1024 950)/2)
    have hp : terminalPayment 949 = (78777633643:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 949+point cut hi 1024 950)/2 = (193671413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193671413:ℝ)/42188800) = (1762499:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193671413:ℝ)/42188800)-4 = (24916213:ℝ)/42188800 by norm_num]
    exact paid_terminal_949
  · change terminalPayment 950 ≤ terminalValue ((point cut hi 1024 950+point cut hi 1024 951)/2)
    have hp : terminalPayment 950 = (77765830691:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 950+point cut hi 1024 951)/2 = (193696563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193696563:ℝ)/42188800) = (1761493:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193696563:ℝ)/42188800)-4 = (24941363:ℝ)/42188800 by norm_num]
    exact paid_terminal_950
  · change terminalPayment 951 ≤ terminalValue ((point cut hi 1024 951+point cut hi 1024 952)/2)
    have hp : terminalPayment 951 = (76752829095:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 951+point cut hi 1024 952)/2 = (193721713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193721713:ℝ)/42188800) = (1760487:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193721713:ℝ)/42188800)-4 = (24966513:ℝ)/42188800 by norm_num]
    exact paid_terminal_951
  · change terminalPayment 952 ≤ terminalValue ((point cut hi 1024 952+point cut hi 1024 953)/2)
    have hp : terminalPayment 952 = (75738627150:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 952+point cut hi 1024 953)/2 = (193746863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193746863:ℝ)/42188800) = (1759481:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193746863:ℝ)/42188800)-4 = (24991663:ℝ)/42188800 by norm_num]
    exact paid_terminal_952
  · change terminalPayment 953 ≤ terminalValue ((point cut hi 1024 953+point cut hi 1024 954)/2)
    have hp : terminalPayment 953 = (74723223151:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 953+point cut hi 1024 954)/2 = (193772013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193772013:ℝ)/42188800) = (1758475:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193772013:ℝ)/42188800)-4 = (25016813:ℝ)/42188800 by norm_num]
    exact paid_terminal_953
  · change terminalPayment 954 ≤ terminalValue ((point cut hi 1024 954+point cut hi 1024 955)/2)
    have hp : terminalPayment 954 = (73706615389:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 954+point cut hi 1024 955)/2 = (193797163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193797163:ℝ)/42188800) = (1757469:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193797163:ℝ)/42188800)-4 = (25041963:ℝ)/42188800 by norm_num]
    exact paid_terminal_954
  · change terminalPayment 955 ≤ terminalValue ((point cut hi 1024 955+point cut hi 1024 956)/2)
    have hp : terminalPayment 955 = (72688802150:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 955+point cut hi 1024 956)/2 = (193822313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193822313:ℝ)/42188800) = (1756463:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193822313:ℝ)/42188800)-4 = (25067113:ℝ)/42188800 by norm_num]
    exact paid_terminal_955
  · change terminalPayment 956 ≤ terminalValue ((point cut hi 1024 956+point cut hi 1024 957)/2)
    have hp : terminalPayment 956 = (71669781718:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 956+point cut hi 1024 957)/2 = (193847463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193847463:ℝ)/42188800) = (1755457:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193847463:ℝ)/42188800)-4 = (25092263:ℝ)/42188800 by norm_num]
    exact paid_terminal_956
  · change terminalPayment 957 ≤ terminalValue ((point cut hi 1024 957+point cut hi 1024 958)/2)
    have hp : terminalPayment 957 = (70649552376:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 957+point cut hi 1024 958)/2 = (193872613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193872613:ℝ)/42188800) = (1754451:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193872613:ℝ)/42188800)-4 = (25117413:ℝ)/42188800 by norm_num]
    exact paid_terminal_957
  · change terminalPayment 958 ≤ terminalValue ((point cut hi 1024 958+point cut hi 1024 959)/2)
    have hp : terminalPayment 958 = (69628112400:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 958+point cut hi 1024 959)/2 = (193897763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193897763:ℝ)/42188800) = (1753445:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193897763:ℝ)/42188800)-4 = (25142563:ℝ)/42188800 by norm_num]
    exact paid_terminal_958
  · change terminalPayment 959 ≤ terminalValue ((point cut hi 1024 959+point cut hi 1024 960)/2)
    have hp : terminalPayment 959 = (68605460066:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 959+point cut hi 1024 960)/2 = (193922913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((193922913:ℝ)/42188800) = (1752439:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((193922913:ℝ)/42188800)-4 = (25167713:ℝ)/42188800 by norm_num]
    exact paid_terminal_959
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_059
