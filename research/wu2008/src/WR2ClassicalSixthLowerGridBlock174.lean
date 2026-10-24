import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints174
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_174 (j : Fin 16) : lowerPayment (16*174+j.val) ≤
    lowerValue ((point 2 split 4096 (16*174+j.val)+point 2 split 4096 (16*174+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2784 ≤ lowerValue ((point 2 split 4096 2784+point 2 split 4096 2785)/2)
    have hp : lowerPayment 2784 = (302248447353:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2784+point 2 split 4096 2785)/2 = (499740939:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499740939:ℝ)/168755200)/ClassicalSixthBranch.v ((499740939:ℝ)/168755200) = (598735251451:ℝ)/286900495512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2784
  · change lowerPayment 2785 ≤ lowerValue ((point 2 split 4096 2785+point 2 split 4096 2786)/2)
    have hp : lowerPayment 2785 = (302336292297:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2785+point 2 split 4096 2786)/2 = (499799201:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499799201:ℝ)/168755200)/ClassicalSixthBranch.v ((499799201:ℝ)/168755200) = (598657937777:ℝ)/286852487624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2785
  · change lowerPayment 2786 ≤ lowerValue ((point 2 split 4096 2786+point 2 split 4096 2787)/2)
    have hp : lowerPayment 2786 = (302424138860:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2786+point 2 split 4096 2787)/2 = (499857463:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499857463:ℝ)/168755200)/ClassicalSixthBranch.v ((499857463:ℝ)/168755200) = (598580624103:ℝ)/286804479736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2786
  · change lowerPayment 2787 ≤ lowerValue ((point 2 split 4096 2787+point 2 split 4096 2788)/2)
    have hp : lowerPayment 2787 = (302511987056:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2787+point 2 split 4096 2788)/2 = (19996629:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19996629:ℝ)/6750208)/ClassicalSixthBranch.v ((19996629:ℝ)/6750208) = (598503310429:ℝ)/286756471848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2787
  · change lowerPayment 2788 ≤ lowerValue ((point 2 split 4096 2788+point 2 split 4096 2789)/2)
    have hp : lowerPayment 2788 = (302599836901:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2788+point 2 split 4096 2789)/2 = (499973987:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499973987:ℝ)/168755200)/ClassicalSixthBranch.v ((499973987:ℝ)/168755200) = (119685199351:ℝ)/57341692792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2788
  · change lowerPayment 2789 ≤ lowerValue ((point 2 split 4096 2789+point 2 split 4096 2790)/2)
    have hp : lowerPayment 2789 = (302687688406:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2789+point 2 split 4096 2790)/2 = (500032249:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500032249:ℝ)/168755200)/ClassicalSixthBranch.v ((500032249:ℝ)/168755200) = (598348683081:ℝ)/286660456072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2789
  · change lowerPayment 2790 ≤ lowerValue ((point 2 split 4096 2790+point 2 split 4096 2791)/2)
    have hp : lowerPayment 2790 = (302775541588:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2790+point 2 split 4096 2791)/2 = (500090511:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500090511:ℝ)/168755200)/ClassicalSixthBranch.v ((500090511:ℝ)/168755200) = (598271369407:ℝ)/286612448184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2790
  · change lowerPayment 2791 ≤ lowerValue ((point 2 split 4096 2791+point 2 split 4096 2792)/2)
    have hp : lowerPayment 2791 = (302863396460:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2791+point 2 split 4096 2792)/2 = (500148773:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500148773:ℝ)/168755200)/ClassicalSixthBranch.v ((500148773:ℝ)/168755200) = (598194055733:ℝ)/286564440296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2791
  · change lowerPayment 2792 ≤ lowerValue ((point 2 split 4096 2792+point 2 split 4096 2793)/2)
    have hp : lowerPayment 2792 = (302951253035:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2792+point 2 split 4096 2793)/2 = (100041407:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100041407:ℝ)/33751040)/ClassicalSixthBranch.v ((100041407:ℝ)/33751040) = (598116742059:ℝ)/286516432408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2792
  · change lowerPayment 2793 ≤ lowerValue ((point 2 split 4096 2793+point 2 split 4096 2794)/2)
    have hp : lowerPayment 2793 = (303039111329:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2793+point 2 split 4096 2794)/2 = (500265297:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500265297:ℝ)/168755200)/ClassicalSixthBranch.v ((500265297:ℝ)/168755200) = (119607885677:ℝ)/57293684904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2793
  · change lowerPayment 2794 ≤ lowerValue ((point 2 split 4096 2794+point 2 split 4096 2795)/2)
    have hp : lowerPayment 2794 = (303126971355:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2794+point 2 split 4096 2795)/2 = (500323559:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500323559:ℝ)/168755200)/ClassicalSixthBranch.v ((500323559:ℝ)/168755200) = (597962114711:ℝ)/286420416632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2794
  · change lowerPayment 2795 ≤ lowerValue ((point 2 split 4096 2795+point 2 split 4096 2796)/2)
    have hp : lowerPayment 2795 = (303214833128:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2795+point 2 split 4096 2796)/2 = (500381821:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500381821:ℝ)/168755200)/ClassicalSixthBranch.v ((500381821:ℝ)/168755200) = (597884801037:ℝ)/286372408744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2795
  · change lowerPayment 2796 ≤ lowerValue ((point 2 split 4096 2796+point 2 split 4096 2797)/2)
    have hp : lowerPayment 2796 = (303302696661:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2796+point 2 split 4096 2797)/2 = (500440083:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500440083:ℝ)/168755200)/ClassicalSixthBranch.v ((500440083:ℝ)/168755200) = (597807487363:ℝ)/286324400856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2796
  · change lowerPayment 2797 ≤ lowerValue ((point 2 split 4096 2797+point 2 split 4096 2798)/2)
    have hp : lowerPayment 2797 = (303390561969:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2797+point 2 split 4096 2798)/2 = (100099669:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100099669:ℝ)/33751040)/ClassicalSixthBranch.v ((100099669:ℝ)/33751040) = (597730173689:ℝ)/286276392968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2797
  · change lowerPayment 2798 ≤ lowerValue ((point 2 split 4096 2798+point 2 split 4096 2799)/2)
    have hp : lowerPayment 2798 = (303478429065:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2798+point 2 split 4096 2799)/2 = (500556607:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500556607:ℝ)/168755200)/ClassicalSixthBranch.v ((500556607:ℝ)/168755200) = (119530572003:ℝ)/57245677016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2798
  · change lowerPayment 2799 ≤ lowerValue ((point 2 split 4096 2799+point 2 split 4096 2800)/2)
    have hp : lowerPayment 2799 = (303566297964:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2799+point 2 split 4096 2800)/2 = (500614869:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((500614869:ℝ)/168755200)/ClassicalSixthBranch.v ((500614869:ℝ)/168755200) = (597575546341:ℝ)/286180377192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2799
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_174
