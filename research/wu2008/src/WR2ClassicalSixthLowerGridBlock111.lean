import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints111
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_111 (j : Fin 16) : lowerPayment (16*111+j.val) ≤
    lowerValue ((point 2 split 4096 (16*111+j.val)+point 2 split 4096 (16*111+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1776 ≤ lowerValue ((point 2 split 4096 1776+point 2 split 4096 1777)/2)
    have hp : lowerPayment 1776 = (212024904790:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1776+point 2 split 4096 1777)/2 = (441012843:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441012843:ℝ)/168755200)/ClassicalSixthBranch.v ((441012843:ℝ)/168755200) = (676667434843:ℝ)/335292446616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1776
  · change lowerPayment 1777 ≤ lowerValue ((point 2 split 4096 1777+point 2 split 4096 1778)/2)
    have hp : lowerPayment 1777 = (212118684939:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1777+point 2 split 4096 1778)/2 = (88214221:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((88214221:ℝ)/33751040)/ClassicalSixthBranch.v ((88214221:ℝ)/33751040) = (676590121169:ℝ)/335244438728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1777
  · change lowerPayment 1778 ≤ lowerValue ((point 2 split 4096 1778+point 2 split 4096 1779)/2)
    have hp : lowerPayment 1778 = (212212451002:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1778+point 2 split 4096 1779)/2 = (441129367:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441129367:ℝ)/168755200)/ClassicalSixthBranch.v ((441129367:ℝ)/168755200) = (135302561499:ℝ)/67039286168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1778
  · change lowerPayment 1779 ≤ lowerValue ((point 2 split 4096 1779+point 2 split 4096 1780)/2)
    have hp : lowerPayment 1779 = (212306202998:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1779+point 2 split 4096 1780)/2 = (441187629:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441187629:ℝ)/168755200)/ClassicalSixthBranch.v ((441187629:ℝ)/168755200) = (676435493821:ℝ)/335148422952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1779
  · change lowerPayment 1780 ≤ lowerValue ((point 2 split 4096 1780+point 2 split 4096 1781)/2)
    have hp : lowerPayment 1780 = (212399940943:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1780+point 2 split 4096 1781)/2 = (441245891:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441245891:ℝ)/168755200)/ClassicalSixthBranch.v ((441245891:ℝ)/168755200) = (676358180147:ℝ)/335100415064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1780
  · change lowerPayment 1781 ≤ lowerValue ((point 2 split 4096 1781+point 2 split 4096 1782)/2)
    have hp : lowerPayment 1781 = (212493664858:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1781+point 2 split 4096 1782)/2 = (441304153:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441304153:ℝ)/168755200)/ClassicalSixthBranch.v ((441304153:ℝ)/168755200) = (676280866473:ℝ)/335052407176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1781
  · change lowerPayment 1782 ≤ lowerValue ((point 2 split 4096 1782+point 2 split 4096 1783)/2)
    have hp : lowerPayment 1782 = (212587374760:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1782+point 2 split 4096 1783)/2 = (88272483:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((88272483:ℝ)/33751040)/ClassicalSixthBranch.v ((88272483:ℝ)/33751040) = (676203552799:ℝ)/335004399288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1782
  · change lowerPayment 1783 ≤ lowerValue ((point 2 split 4096 1783+point 2 split 4096 1784)/2)
    have hp : lowerPayment 1783 = (212681070668:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1783+point 2 split 4096 1784)/2 = (441420677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441420677:ℝ)/168755200)/ClassicalSixthBranch.v ((441420677:ℝ)/168755200) = (27045049565:ℝ)/13398255656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1783
  · change lowerPayment 1784 ≤ lowerValue ((point 2 split 4096 1784+point 2 split 4096 1785)/2)
    have hp : lowerPayment 1784 = (212774752600:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1784+point 2 split 4096 1785)/2 = (441478939:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441478939:ℝ)/168755200)/ClassicalSixthBranch.v ((441478939:ℝ)/168755200) = (676048925451:ℝ)/334908383512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1784
  · change lowerPayment 1785 ≤ lowerValue ((point 2 split 4096 1785+point 2 split 4096 1786)/2)
    have hp : lowerPayment 1785 = (212868420574:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1785+point 2 split 4096 1786)/2 = (441537201:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441537201:ℝ)/168755200)/ClassicalSixthBranch.v ((441537201:ℝ)/168755200) = (675971611777:ℝ)/334860375624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1785
  · change lowerPayment 1786 ≤ lowerValue ((point 2 split 4096 1786+point 2 split 4096 1787)/2)
    have hp : lowerPayment 1786 = (212962074609:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1786+point 2 split 4096 1787)/2 = (441595463:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441595463:ℝ)/168755200)/ClassicalSixthBranch.v ((441595463:ℝ)/168755200) = (675894298103:ℝ)/334812367736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1786
  · change lowerPayment 1787 ≤ lowerValue ((point 2 split 4096 1787+point 2 split 4096 1788)/2)
    have hp : lowerPayment 1787 = (213055714723:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1787+point 2 split 4096 1788)/2 = (17666149:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((17666149:ℝ)/6750208)/ClassicalSixthBranch.v ((17666149:ℝ)/6750208) = (675816984429:ℝ)/334764359848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1787
  · change lowerPayment 1788 ≤ lowerValue ((point 2 split 4096 1788+point 2 split 4096 1789)/2)
    have hp : lowerPayment 1788 = (213149340935:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1788+point 2 split 4096 1789)/2 = (441711987:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441711987:ℝ)/168755200)/ClassicalSixthBranch.v ((441711987:ℝ)/168755200) = (135147934151:ℝ)/66943270392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1788
  · change lowerPayment 1789 ≤ lowerValue ((point 2 split 4096 1789+point 2 split 4096 1790)/2)
    have hp : lowerPayment 1789 = (213242953262:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1789+point 2 split 4096 1790)/2 = (441770249:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441770249:ℝ)/168755200)/ClassicalSixthBranch.v ((441770249:ℝ)/168755200) = (675662357081:ℝ)/334668344072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1789
  · change lowerPayment 1790 ≤ lowerValue ((point 2 split 4096 1790+point 2 split 4096 1791)/2)
    have hp : lowerPayment 1790 = (213336551723:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1790+point 2 split 4096 1791)/2 = (441828511:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441828511:ℝ)/168755200)/ClassicalSixthBranch.v ((441828511:ℝ)/168755200) = (675585043407:ℝ)/334620336184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1790
  · change lowerPayment 1791 ≤ lowerValue ((point 2 split 4096 1791+point 2 split 4096 1792)/2)
    have hp : lowerPayment 1791 = (213430136336:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1791+point 2 split 4096 1792)/2 = (441886773:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((441886773:ℝ)/168755200)/ClassicalSixthBranch.v ((441886773:ℝ)/168755200) = (675507729733:ℝ)/334572328296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1791
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_111
