import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints176
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_176 (j : Fin 16) : lowerPayment (16*176+j.val) ≤
    lowerValue ((point 2 split 4096 (16*176+j.val)+point 2 split 4096 (16*176+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2816 ≤ lowerValue ((point 2 split 4096 2816+point 2 split 4096 2817)/2)
    have hp : lowerPayment 2816 = (305060358771:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2816+point 2 split 4096 2817)/2 = (501605323:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501605323:ℝ)/168755200)/ClassicalSixthBranch.v ((501605323:ℝ)/168755200) = (596261213883:ℝ)/285364243096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2816
  · change lowerPayment 2817 ≤ lowerValue ((point 2 split 4096 2817+point 2 split 4096 2818)/2)
    have hp : lowerPayment 2817 = (305148262536:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2817+point 2 split 4096 2818)/2 = (100332717:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100332717:ℝ)/33751040)/ClassicalSixthBranch.v ((100332717:ℝ)/33751040) = (596183900209:ℝ)/285316235208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2817
  · change lowerPayment 2818 ≤ lowerValue ((point 2 split 4096 2818+point 2 split 4096 2819)/2)
    have hp : lowerPayment 2818 = (305236168371:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2818+point 2 split 4096 2819)/2 = (501721847:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501721847:ℝ)/168755200)/ClassicalSixthBranch.v ((501721847:ℝ)/168755200) = (119221317307:ℝ)/57053645464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2818
  · change lowerPayment 2819 ≤ lowerValue ((point 2 split 4096 2819+point 2 split 4096 2820)/2)
    have hp : lowerPayment 2819 = (305324076292:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2819+point 2 split 4096 2820)/2 = (501780109:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501780109:ℝ)/168755200)/ClassicalSixthBranch.v ((501780109:ℝ)/168755200) = (596029272861:ℝ)/285220219432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2819
  · change lowerPayment 2820 ≤ lowerValue ((point 2 split 4096 2820+point 2 split 4096 2821)/2)
    have hp : lowerPayment 2820 = (305411986312:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2820+point 2 split 4096 2821)/2 = (501838371:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501838371:ℝ)/168755200)/ClassicalSixthBranch.v ((501838371:ℝ)/168755200) = (595951959187:ℝ)/285172211544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2820
  · change lowerPayment 2821 ≤ lowerValue ((point 2 split 4096 2821+point 2 split 4096 2822)/2)
    have hp : lowerPayment 2821 = (305499898446:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2821+point 2 split 4096 2822)/2 = (501896633:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((501896633:ℝ)/168755200)/ClassicalSixthBranch.v ((501896633:ℝ)/168755200) = (595874645513:ℝ)/285124203656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2821
  · change lowerPayment 2822 ≤ lowerValue ((point 2 split 4096 2822+point 2 split 4096 2823)/2)
    have hp : lowerPayment 2822 = (305587812707:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2822+point 2 split 4096 2823)/2 = (100390979:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100390979:ℝ)/33751040)/ClassicalSixthBranch.v ((100390979:ℝ)/33751040) = (595797331839:ℝ)/285076195768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2822
  · change lowerPayment 2823 ≤ lowerValue ((point 2 split 4096 2823+point 2 split 4096 2824)/2)
    have hp : lowerPayment 2823 = (305675729109:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2823+point 2 split 4096 2824)/2 = (502013157:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502013157:ℝ)/168755200)/ClassicalSixthBranch.v ((502013157:ℝ)/168755200) = (119144003633:ℝ)/57005637576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2823
  · change lowerPayment 2824 ≤ lowerValue ((point 2 split 4096 2824+point 2 split 4096 2825)/2)
    have hp : lowerPayment 2824 = (305763647667:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2824+point 2 split 4096 2825)/2 = (502071419:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502071419:ℝ)/168755200)/ClassicalSixthBranch.v ((502071419:ℝ)/168755200) = (595642704491:ℝ)/284980179992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2824
  · change lowerPayment 2825 ≤ lowerValue ((point 2 split 4096 2825+point 2 split 4096 2826)/2)
    have hp : lowerPayment 2825 = (305851568395:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2825+point 2 split 4096 2826)/2 = (502129681:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502129681:ℝ)/168755200)/ClassicalSixthBranch.v ((502129681:ℝ)/168755200) = (595565390817:ℝ)/284932172104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2825
  · change lowerPayment 2826 ≤ lowerValue ((point 2 split 4096 2826+point 2 split 4096 2827)/2)
    have hp : lowerPayment 2826 = (305939491307:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2826+point 2 split 4096 2827)/2 = (502187943:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502187943:ℝ)/168755200)/ClassicalSixthBranch.v ((502187943:ℝ)/168755200) = (595488077143:ℝ)/284884164216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2826
  · change lowerPayment 2827 ≤ lowerValue ((point 2 split 4096 2827+point 2 split 4096 2828)/2)
    have hp : lowerPayment 2827 = (306027416417:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2827+point 2 split 4096 2828)/2 = (100449241:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100449241:ℝ)/33751040)/ClassicalSixthBranch.v ((100449241:ℝ)/33751040) = (595410763469:ℝ)/284836156328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2827
  · change lowerPayment 2828 ≤ lowerValue ((point 2 split 4096 2828+point 2 split 4096 2829)/2)
    have hp : lowerPayment 2828 = (306115343739:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2828+point 2 split 4096 2829)/2 = (502304467:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502304467:ℝ)/168755200)/ClassicalSixthBranch.v ((502304467:ℝ)/168755200) = (119066689959:ℝ)/56957629688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2828
  · change lowerPayment 2829 ≤ lowerValue ((point 2 split 4096 2829+point 2 split 4096 2830)/2)
    have hp : lowerPayment 2829 = (306203273288:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2829+point 2 split 4096 2830)/2 = (502362729:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502362729:ℝ)/168755200)/ClassicalSixthBranch.v ((502362729:ℝ)/168755200) = (595256136121:ℝ)/284740140552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2829
  · change lowerPayment 2830 ≤ lowerValue ((point 2 split 4096 2830+point 2 split 4096 2831)/2)
    have hp : lowerPayment 2830 = (306291205076:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2830+point 2 split 4096 2831)/2 = (502420991:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502420991:ℝ)/168755200)/ClassicalSixthBranch.v ((502420991:ℝ)/168755200) = (595178822447:ℝ)/284692132664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2830
  · change lowerPayment 2831 ≤ lowerValue ((point 2 split 4096 2831+point 2 split 4096 2832)/2)
    have hp : lowerPayment 2831 = (306379139119:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2831+point 2 split 4096 2832)/2 = (502479253:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((502479253:ℝ)/168755200)/ClassicalSixthBranch.v ((502479253:ℝ)/168755200) = (595101508773:ℝ)/284644124776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2831
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_176
