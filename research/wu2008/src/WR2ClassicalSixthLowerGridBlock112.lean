import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints112
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_112 (j : Fin 16) : lowerPayment (16*112+j.val) ≤
    lowerValue ((point 2 split 4096 (16*112+j.val)+point 2 split 4096 (16*112+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1792 ≤ lowerValue ((point 2 split 4096 1792+point 2 split 4096 1793)/2)
    have hp : lowerPayment 1792 = (213523707120:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1792+point 2 split 4096 1793)/2 = (88389007:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((88389007:ℝ)/33751040)/ClassicalSixthBranch.v ((88389007:ℝ)/33751040) = (675430416059:ℝ)/334524320408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1792
  · change lowerPayment 1793 ≤ lowerValue ((point 2 split 4096 1793+point 2 split 4096 1794)/2)
    have hp : lowerPayment 1793 = (213617264092:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1793+point 2 split 4096 1794)/2 = (442003297:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442003297:ℝ)/168755200)/ClassicalSixthBranch.v ((442003297:ℝ)/168755200) = (135070620477:ℝ)/66895262504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1793
  · change lowerPayment 1794 ≤ lowerValue ((point 2 split 4096 1794+point 2 split 4096 1795)/2)
    have hp : lowerPayment 1794 = (213710807272:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1794+point 2 split 4096 1795)/2 = (442061559:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442061559:ℝ)/168755200)/ClassicalSixthBranch.v ((442061559:ℝ)/168755200) = (675275788711:ℝ)/334428304632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1794
  · change lowerPayment 1795 ≤ lowerValue ((point 2 split 4096 1795+point 2 split 4096 1796)/2)
    have hp : lowerPayment 1795 = (213804336677:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1795+point 2 split 4096 1796)/2 = (442119821:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442119821:ℝ)/168755200)/ClassicalSixthBranch.v ((442119821:ℝ)/168755200) = (675198475037:ℝ)/334380296744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1795
  · change lowerPayment 1796 ≤ lowerValue ((point 2 split 4096 1796+point 2 split 4096 1797)/2)
    have hp : lowerPayment 1796 = (213897852326:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1796+point 2 split 4096 1797)/2 = (442178083:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442178083:ℝ)/168755200)/ClassicalSixthBranch.v ((442178083:ℝ)/168755200) = (675121161363:ℝ)/334332288856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1796
  · change lowerPayment 1797 ≤ lowerValue ((point 2 split 4096 1797+point 2 split 4096 1798)/2)
    have hp : lowerPayment 1797 = (213991354236:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1797+point 2 split 4096 1798)/2 = (88447269:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((88447269:ℝ)/33751040)/ClassicalSixthBranch.v ((88447269:ℝ)/33751040) = (675043847689:ℝ)/334284280968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1797
  · change lowerPayment 1798 ≤ lowerValue ((point 2 split 4096 1798+point 2 split 4096 1799)/2)
    have hp : lowerPayment 1798 = (214084842426:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1798+point 2 split 4096 1799)/2 = (442294607:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442294607:ℝ)/168755200)/ClassicalSixthBranch.v ((442294607:ℝ)/168755200) = (134993306803:ℝ)/66847254616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1798
  · change lowerPayment 1799 ≤ lowerValue ((point 2 split 4096 1799+point 2 split 4096 1800)/2)
    have hp : lowerPayment 1799 = (214178316915:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1799+point 2 split 4096 1800)/2 = (442352869:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442352869:ℝ)/168755200)/ClassicalSixthBranch.v ((442352869:ℝ)/168755200) = (674889220341:ℝ)/334188265192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1799
  · change lowerPayment 1800 ≤ lowerValue ((point 2 split 4096 1800+point 2 split 4096 1801)/2)
    have hp : lowerPayment 1800 = (214271777720:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1800+point 2 split 4096 1801)/2 = (442411131:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442411131:ℝ)/168755200)/ClassicalSixthBranch.v ((442411131:ℝ)/168755200) = (674811906667:ℝ)/334140257304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1800
  · change lowerPayment 1801 ≤ lowerValue ((point 2 split 4096 1801+point 2 split 4096 1802)/2)
    have hp : lowerPayment 1801 = (214365224860:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1801+point 2 split 4096 1802)/2 = (442469393:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442469393:ℝ)/168755200)/ClassicalSixthBranch.v ((442469393:ℝ)/168755200) = (674734592993:ℝ)/334092249416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1801
  · change lowerPayment 1802 ≤ lowerValue ((point 2 split 4096 1802+point 2 split 4096 1803)/2)
    have hp : lowerPayment 1802 = (214458658353:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1802+point 2 split 4096 1803)/2 = (859277:ℝ)/327680 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((859277:ℝ)/327680)/ClassicalSixthBranch.v ((859277:ℝ)/327680) = (6550070673:ℝ)/3243147976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1802
  · change lowerPayment 1803 ≤ lowerValue ((point 2 split 4096 1803+point 2 split 4096 1804)/2)
    have hp : lowerPayment 1803 = (214552078217:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1803+point 2 split 4096 1804)/2 = (442585917:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442585917:ℝ)/168755200)/ClassicalSixthBranch.v ((442585917:ℝ)/168755200) = (134915993129:ℝ)/66799246728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1803
  · change lowerPayment 1804 ≤ lowerValue ((point 2 split 4096 1804+point 2 split 4096 1805)/2)
    have hp : lowerPayment 1804 = (214645484470:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1804+point 2 split 4096 1805)/2 = (442644179:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442644179:ℝ)/168755200)/ClassicalSixthBranch.v ((442644179:ℝ)/168755200) = (674502651971:ℝ)/333948225752 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1804
  · change lowerPayment 1805 ≤ lowerValue ((point 2 split 4096 1805+point 2 split 4096 1806)/2)
    have hp : lowerPayment 1805 = (214738877131:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1805+point 2 split 4096 1806)/2 = (442702441:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442702441:ℝ)/168755200)/ClassicalSixthBranch.v ((442702441:ℝ)/168755200) = (674425338297:ℝ)/333900217864 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1805
  · change lowerPayment 1806 ≤ lowerValue ((point 2 split 4096 1806+point 2 split 4096 1807)/2)
    have hp : lowerPayment 1806 = (214832256217:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1806+point 2 split 4096 1807)/2 = (442760703:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((442760703:ℝ)/168755200)/ClassicalSixthBranch.v ((442760703:ℝ)/168755200) = (674348024623:ℝ)/333852209976 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1806
  · change lowerPayment 1807 ≤ lowerValue ((point 2 split 4096 1807+point 2 split 4096 1808)/2)
    have hp : lowerPayment 1807 = (214925621747:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1807+point 2 split 4096 1808)/2 = (88563793:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((88563793:ℝ)/33751040)/ClassicalSixthBranch.v ((88563793:ℝ)/33751040) = (674270710949:ℝ)/333804202088 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1807
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_112
