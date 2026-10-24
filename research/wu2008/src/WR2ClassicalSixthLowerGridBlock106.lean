import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints106
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_106 (j : Fin 16) : lowerPayment (16*106+j.val) ≤
    lowerValue ((point 2 split 4096 (16*106+j.val)+point 2 split 4096 (16*106+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1696 ≤ lowerValue ((point 2 split 4096 1696+point 2 split 4096 1697)/2)
    have hp : lowerPayment 1696 = (204475207982:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1696+point 2 split 4096 1697)/2 = (436351883:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436351883:ℝ)/168755200)/ClassicalSixthBranch.v ((436351883:ℝ)/168755200) = (682852528763:ℝ)/339133077656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1696
  · change lowerPayment 1697 ≤ lowerValue ((point 2 split 4096 1697+point 2 split 4096 1698)/2)
    have hp : lowerPayment 1697 = (204570175425:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1697+point 2 split 4096 1698)/2 = (87282029:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87282029:ℝ)/33751040)/ClassicalSixthBranch.v ((87282029:ℝ)/33751040) = (682775215089:ℝ)/339085069768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1697
  · change lowerPayment 1698 ≤ lowerValue ((point 2 split 4096 1698+point 2 split 4096 1699)/2)
    have hp : lowerPayment 1698 = (204665127281:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1698+point 2 split 4096 1699)/2 = (436468407:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436468407:ℝ)/168755200)/ClassicalSixthBranch.v ((436468407:ℝ)/168755200) = (136539580283:ℝ)/67807412376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1698
  · change lowerPayment 1699 ≤ lowerValue ((point 2 split 4096 1699+point 2 split 4096 1700)/2)
    have hp : lowerPayment 1699 = (204760063568:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1699+point 2 split 4096 1700)/2 = (4238123:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4238123:ℝ)/1638400)/ClassicalSixthBranch.v ((4238123:ℝ)/1638400) = (6627384347:ℝ)/3291155864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1699
  · change lowerPayment 1700 ≤ lowerValue ((point 2 split 4096 1700+point 2 split 4096 1701)/2)
    have hp : lowerPayment 1700 = (204854984307:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1700+point 2 split 4096 1701)/2 = (436584931:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436584931:ℝ)/168755200)/ClassicalSixthBranch.v ((436584931:ℝ)/168755200) = (682543274067:ℝ)/338941046104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1700
  · change lowerPayment 1701 ≤ lowerValue ((point 2 split 4096 1701+point 2 split 4096 1702)/2)
    have hp : lowerPayment 1701 = (204949889516:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1701+point 2 split 4096 1702)/2 = (436643193:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436643193:ℝ)/168755200)/ClassicalSixthBranch.v ((436643193:ℝ)/168755200) = (682465960393:ℝ)/338893038216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1701
  · change lowerPayment 1702 ≤ lowerValue ((point 2 split 4096 1702+point 2 split 4096 1703)/2)
    have hp : lowerPayment 1702 = (205044779214:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1702+point 2 split 4096 1703)/2 = (87340291:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87340291:ℝ)/33751040)/ClassicalSixthBranch.v ((87340291:ℝ)/33751040) = (682388646719:ℝ)/338845030328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1702
  · change lowerPayment 1703 ≤ lowerValue ((point 2 split 4096 1703+point 2 split 4096 1704)/2)
    have hp : lowerPayment 1703 = (205139653421:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1703+point 2 split 4096 1704)/2 = (436759717:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436759717:ℝ)/168755200)/ClassicalSixthBranch.v ((436759717:ℝ)/168755200) = (136462266609:ℝ)/67759404488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1703
  · change lowerPayment 1704 ≤ lowerValue ((point 2 split 4096 1704+point 2 split 4096 1705)/2)
    have hp : lowerPayment 1704 = (205234512155:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1704+point 2 split 4096 1705)/2 = (436817979:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436817979:ℝ)/168755200)/ClassicalSixthBranch.v ((436817979:ℝ)/168755200) = (682234019371:ℝ)/338749014552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1704
  · change lowerPayment 1705 ≤ lowerValue ((point 2 split 4096 1705+point 2 split 4096 1706)/2)
    have hp : lowerPayment 1705 = (205329355436:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1705+point 2 split 4096 1706)/2 = (436876241:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436876241:ℝ)/168755200)/ClassicalSixthBranch.v ((436876241:ℝ)/168755200) = (682156705697:ℝ)/338701006664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1705
  · change lowerPayment 1706 ≤ lowerValue ((point 2 split 4096 1706+point 2 split 4096 1707)/2)
    have hp : lowerPayment 1706 = (205424183282:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1706+point 2 split 4096 1707)/2 = (436934503:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((436934503:ℝ)/168755200)/ClassicalSixthBranch.v ((436934503:ℝ)/168755200) = (682079392023:ℝ)/338652998776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1706
  · change lowerPayment 1707 ≤ lowerValue ((point 2 split 4096 1707+point 2 split 4096 1708)/2)
    have hp : lowerPayment 1707 = (205518995713:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1707+point 2 split 4096 1708)/2 = (87398553:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((87398553:ℝ)/33751040)/ClassicalSixthBranch.v ((87398553:ℝ)/33751040) = (682002078349:ℝ)/338604990888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1707
  · change lowerPayment 1708 ≤ lowerValue ((point 2 split 4096 1708+point 2 split 4096 1709)/2)
    have hp : lowerPayment 1708 = (205613792748:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1708+point 2 split 4096 1709)/2 = (437051027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437051027:ℝ)/168755200)/ClassicalSixthBranch.v ((437051027:ℝ)/168755200) = (27276990587:ℝ)/13542279320 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1708
  · change lowerPayment 1709 ≤ lowerValue ((point 2 split 4096 1709+point 2 split 4096 1710)/2)
    have hp : lowerPayment 1709 = (205708574405:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1709+point 2 split 4096 1710)/2 = (437109289:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437109289:ℝ)/168755200)/ClassicalSixthBranch.v ((437109289:ℝ)/168755200) = (681847451001:ℝ)/338508975112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1709
  · change lowerPayment 1710 ≤ lowerValue ((point 2 split 4096 1710+point 2 split 4096 1711)/2)
    have hp : lowerPayment 1710 = (205803340704:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1710+point 2 split 4096 1711)/2 = (437167551:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437167551:ℝ)/168755200)/ClassicalSixthBranch.v ((437167551:ℝ)/168755200) = (681770137327:ℝ)/338460967224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1710
  · change lowerPayment 1711 ≤ lowerValue ((point 2 split 4096 1711+point 2 split 4096 1712)/2)
    have hp : lowerPayment 1711 = (205898091664:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1711+point 2 split 4096 1712)/2 = (437225813:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((437225813:ℝ)/168755200)/ClassicalSixthBranch.v ((437225813:ℝ)/168755200) = (681692823653:ℝ)/338412959336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1711
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_106
