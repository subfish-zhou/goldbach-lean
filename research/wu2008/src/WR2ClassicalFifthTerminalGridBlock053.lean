import WR2ClassicalFifthTerminalPayments
import WR2ClassicalFifthTerminalPoints053
noncomputable section
namespace WuPaper.ClassicalFifthRational
open ClassicalFifthSource ClassicalUniformMidpoint
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem terminal_grid_block_053 (j : Fin 16) : terminalPayment (16*53+j.val) ≤
    terminalValue ((point cut hi 1024 (16*53+j.val)+point cut hi 1024 (16*53+j.val+1))/2) := by
  fin_cases j
  · change terminalPayment 848 ≤ terminalValue ((point cut hi 1024 848+point cut hi 1024 849)/2)
    have hp : terminalPayment 848 = (175082692080:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 848+point cut hi 1024 849)/2 = (191131263:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191131263:ℝ)/42188800) = (1864105:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191131263:ℝ)/42188800)-4 = (22376063:ℝ)/42188800 by norm_num]
    exact paid_terminal_848
  · change terminalPayment 849 ≤ terminalValue ((point cut hi 1024 849+point cut hi 1024 850)/2)
    have hp : terminalPayment 849 = (174183712598:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 849+point cut hi 1024 850)/2 = (191156413:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191156413:ℝ)/42188800) = (1863099:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191156413:ℝ)/42188800)-4 = (22401213:ℝ)/42188800 by norm_num]
    exact paid_terminal_849
  · change terminalPayment 850 ≤ terminalValue ((point cut hi 1024 850+point cut hi 1024 851)/2)
    have hp : terminalPayment 850 = (173283691242:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 850+point cut hi 1024 851)/2 = (191181563:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191181563:ℝ)/42188800) = (1862093:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191181563:ℝ)/42188800)-4 = (22426363:ℝ)/42188800 by norm_num]
    exact paid_terminal_850
  · change terminalPayment 851 ≤ terminalValue ((point cut hi 1024 851+point cut hi 1024 852)/2)
    have hp : terminalPayment 851 = (172382626598:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 851+point cut hi 1024 852)/2 = (191206713:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191206713:ℝ)/42188800) = (1861087:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191206713:ℝ)/42188800)-4 = (22451513:ℝ)/42188800 by norm_num]
    exact paid_terminal_851
  · change terminalPayment 852 ≤ terminalValue ((point cut hi 1024 852+point cut hi 1024 853)/2)
    have hp : terminalPayment 852 = (171480517249:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 852+point cut hi 1024 853)/2 = (191231863:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191231863:ℝ)/42188800) = (1860081:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191231863:ℝ)/42188800)-4 = (22476663:ℝ)/42188800 by norm_num]
    exact paid_terminal_852
  · change terminalPayment 853 ≤ terminalValue ((point cut hi 1024 853+point cut hi 1024 854)/2)
    have hp : terminalPayment 853 = (170577361774:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 853+point cut hi 1024 854)/2 = (191257013:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191257013:ℝ)/42188800) = (1859075:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191257013:ℝ)/42188800)-4 = (22501813:ℝ)/42188800 by norm_num]
    exact paid_terminal_853
  · change terminalPayment 854 ≤ terminalValue ((point cut hi 1024 854+point cut hi 1024 855)/2)
    have hp : terminalPayment 854 = (169673158751:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 854+point cut hi 1024 855)/2 = (191282163:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191282163:ℝ)/42188800) = (1858069:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191282163:ℝ)/42188800)-4 = (22526963:ℝ)/42188800 by norm_num]
    exact paid_terminal_854
  · change terminalPayment 855 ≤ terminalValue ((point cut hi 1024 855+point cut hi 1024 856)/2)
    have hp : terminalPayment 855 = (168767906754:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 855+point cut hi 1024 856)/2 = (191307313:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191307313:ℝ)/42188800) = (1857063:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191307313:ℝ)/42188800)-4 = (22552113:ℝ)/42188800 by norm_num]
    exact paid_terminal_855
  · change terminalPayment 856 ≤ terminalValue ((point cut hi 1024 856+point cut hi 1024 857)/2)
    have hp : terminalPayment 856 = (167861604356:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 856+point cut hi 1024 857)/2 = (191332463:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191332463:ℝ)/42188800) = (1856057:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191332463:ℝ)/42188800)-4 = (22577263:ℝ)/42188800 by norm_num]
    exact paid_terminal_856
  · change terminalPayment 857 ≤ terminalValue ((point cut hi 1024 857+point cut hi 1024 858)/2)
    have hp : terminalPayment 857 = (166954250127:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 857+point cut hi 1024 858)/2 = (191357613:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191357613:ℝ)/42188800) = (1855051:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191357613:ℝ)/42188800)-4 = (22602413:ℝ)/42188800 by norm_num]
    exact paid_terminal_857
  · change terminalPayment 858 ≤ terminalValue ((point cut hi 1024 858+point cut hi 1024 859)/2)
    have hp : terminalPayment 858 = (166045842634:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 858+point cut hi 1024 859)/2 = (191382763:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191382763:ℝ)/42188800) = (1854045:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191382763:ℝ)/42188800)-4 = (22627563:ℝ)/42188800 by norm_num]
    exact paid_terminal_858
  · change terminalPayment 859 ≤ terminalValue ((point cut hi 1024 859+point cut hi 1024 860)/2)
    have hp : terminalPayment 859 = (165136380440:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 859+point cut hi 1024 860)/2 = (191407913:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191407913:ℝ)/42188800) = (1853039:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191407913:ℝ)/42188800)-4 = (22652713:ℝ)/42188800 by norm_num]
    exact paid_terminal_859
  · change terminalPayment 860 ≤ terminalValue ((point cut hi 1024 860+point cut hi 1024 861)/2)
    have hp : terminalPayment 860 = (164225862108:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 860+point cut hi 1024 861)/2 = (191433063:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191433063:ℝ)/42188800) = (1852033:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191433063:ℝ)/42188800)-4 = (22677863:ℝ)/42188800 by norm_num]
    exact paid_terminal_860
  · change terminalPayment 861 ≤ terminalValue ((point cut hi 1024 861+point cut hi 1024 862)/2)
    have hp : terminalPayment 861 = (163314286198:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 861+point cut hi 1024 862)/2 = (191458213:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191458213:ℝ)/42188800) = (1851027:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191458213:ℝ)/42188800)-4 = (22703013:ℝ)/42188800 by norm_num]
    exact paid_terminal_861
  · change terminalPayment 862 ≤ terminalValue ((point cut hi 1024 862+point cut hi 1024 863)/2)
    have hp : terminalPayment 862 = (162401651266:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 862+point cut hi 1024 863)/2 = (191483363:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191483363:ℝ)/42188800) = (1850021:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191483363:ℝ)/42188800)-4 = (22728163:ℝ)/42188800 by norm_num]
    exact paid_terminal_862
  · change terminalPayment 863 ≤ terminalValue ((point cut hi 1024 863+point cut hi 1024 864)/2)
    have hp : terminalPayment 863 = (161487955866:ℝ)/1000000000000 := rfl
    have hx : (point cut hi 1024 863+point cut hi 1024 864)/2 = (191508513:ℝ)/42188800 := by
      norm_num [point,step,lo,cut,hi,WuSource.SrcSixthGain.split,WuSource.SrcSixthGain.endpoint,
        ClassicalFifthBranch.endpoint,ClassicalSixthBranch.R,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((191508513:ℝ)/42188800) = (1849015:ℝ)/1687552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold terminalValue
    rw [hr]
    rw [show ((191508513:ℝ)/42188800)-4 = (22753313:ℝ)/42188800 by norm_num]
    exact paid_terminal_863
end WuPaper.ClassicalFifthRational
#print axioms WuPaper.ClassicalFifthRational.terminal_grid_block_053
