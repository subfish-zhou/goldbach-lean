import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints051
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_051 (j : Fin 16) : lowerPayment (16*51+j.val) ≤
    lowerValue ((point 2 split 4096 (16*51+j.val)+point 2 split 4096 (16*51+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 816 ≤ lowerValue ((point 2 split 4096 816+point 2 split 4096 817)/2)
    have hp : lowerPayment 816 = (112376025288:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 816+point 2 split 4096 817)/2 = (385081323:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385081323:ℝ)/168755200)/ClassicalSixthBranch.v ((385081323:ℝ)/168755200) = (750888561883:ℝ)/381380019096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_816
  · change lowerPayment 817 ≤ lowerValue ((point 2 split 4096 817+point 2 split 4096 818)/2)
    have hp : lowerPayment 817 = (112493590830:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 817+point 2 split 4096 818)/2 = (77027917:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77027917:ℝ)/33751040)/ClassicalSixthBranch.v ((77027917:ℝ)/33751040) = (750811248209:ℝ)/381332011208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_817
  · change lowerPayment 818 ≤ lowerValue ((point 2 split 4096 818+point 2 split 4096 819)/2)
    have hp : lowerPayment 818 = (112611118466:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 818+point 2 split 4096 819)/2 = (385197847:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385197847:ℝ)/168755200)/ClassicalSixthBranch.v ((385197847:ℝ)/168755200) = (150146786907:ℝ)/76256800664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_818
  · change lowerPayment 819 ≤ lowerValue ((point 2 split 4096 819+point 2 split 4096 820)/2)
    have hp : lowerPayment 819 = (112728608229:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 819+point 2 split 4096 820)/2 = (385256109:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385256109:ℝ)/168755200)/ClassicalSixthBranch.v ((385256109:ℝ)/168755200) = (750656620861:ℝ)/381235995432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_819
  · change lowerPayment 820 ≤ lowerValue ((point 2 split 4096 820+point 2 split 4096 821)/2)
    have hp : lowerPayment 820 = (112846060154:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 820+point 2 split 4096 821)/2 = (385314371:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385314371:ℝ)/168755200)/ClassicalSixthBranch.v ((385314371:ℝ)/168755200) = (750579307187:ℝ)/381187987544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_820
  · change lowerPayment 821 ≤ lowerValue ((point 2 split 4096 821+point 2 split 4096 822)/2)
    have hp : lowerPayment 821 = (112963474274:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 821+point 2 split 4096 822)/2 = (385372633:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385372633:ℝ)/168755200)/ClassicalSixthBranch.v ((385372633:ℝ)/168755200) = (750501993513:ℝ)/381139979656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_821
  · change lowerPayment 822 ≤ lowerValue ((point 2 split 4096 822+point 2 split 4096 823)/2)
    have hp : lowerPayment 822 = (113080850624:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 822+point 2 split 4096 823)/2 = (77086179:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77086179:ℝ)/33751040)/ClassicalSixthBranch.v ((77086179:ℝ)/33751040) = (750424679839:ℝ)/381091971768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_822
  · change lowerPayment 823 ≤ lowerValue ((point 2 split 4096 823+point 2 split 4096 824)/2)
    have hp : lowerPayment 823 = (113198189238:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 823+point 2 split 4096 824)/2 = (385489157:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385489157:ℝ)/168755200)/ClassicalSixthBranch.v ((385489157:ℝ)/168755200) = (150069473233:ℝ)/76208792776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_823
  · change lowerPayment 824 ≤ lowerValue ((point 2 split 4096 824+point 2 split 4096 825)/2)
    have hp : lowerPayment 824 = (113315490150:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 824+point 2 split 4096 825)/2 = (385547419:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385547419:ℝ)/168755200)/ClassicalSixthBranch.v ((385547419:ℝ)/168755200) = (750270052491:ℝ)/380995955992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_824
  · change lowerPayment 825 ≤ lowerValue ((point 2 split 4096 825+point 2 split 4096 826)/2)
    have hp : lowerPayment 825 = (113432753393:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 825+point 2 split 4096 826)/2 = (385605681:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385605681:ℝ)/168755200)/ClassicalSixthBranch.v ((385605681:ℝ)/168755200) = (750192738817:ℝ)/380947948104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_825
  · change lowerPayment 826 ≤ lowerValue ((point 2 split 4096 826+point 2 split 4096 827)/2)
    have hp : lowerPayment 826 = (113549979001:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 826+point 2 split 4096 827)/2 = (385663943:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385663943:ℝ)/168755200)/ClassicalSixthBranch.v ((385663943:ℝ)/168755200) = (750115425143:ℝ)/380899940216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_826
  · change lowerPayment 827 ≤ lowerValue ((point 2 split 4096 827+point 2 split 4096 828)/2)
    have hp : lowerPayment 827 = (113667167009:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 827+point 2 split 4096 828)/2 = (77144441:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77144441:ℝ)/33751040)/ClassicalSixthBranch.v ((77144441:ℝ)/33751040) = (750038111469:ℝ)/380851932328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_827
  · change lowerPayment 828 ≤ lowerValue ((point 2 split 4096 828+point 2 split 4096 829)/2)
    have hp : lowerPayment 828 = (113784317450:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 828+point 2 split 4096 829)/2 = (385780467:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385780467:ℝ)/168755200)/ClassicalSixthBranch.v ((385780467:ℝ)/168755200) = (149992159559:ℝ)/76160784888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_828
  · change lowerPayment 829 ≤ lowerValue ((point 2 split 4096 829+point 2 split 4096 830)/2)
    have hp : lowerPayment 829 = (113901430359:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 829+point 2 split 4096 830)/2 = (385838729:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385838729:ℝ)/168755200)/ClassicalSixthBranch.v ((385838729:ℝ)/168755200) = (749883484121:ℝ)/380755916552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_829
  · change lowerPayment 830 ≤ lowerValue ((point 2 split 4096 830+point 2 split 4096 831)/2)
    have hp : lowerPayment 830 = (114018505768:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 830+point 2 split 4096 831)/2 = (385896991:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385896991:ℝ)/168755200)/ClassicalSixthBranch.v ((385896991:ℝ)/168755200) = (749806170447:ℝ)/380707908664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_830
  · change lowerPayment 831 ≤ lowerValue ((point 2 split 4096 831+point 2 split 4096 832)/2)
    have hp : lowerPayment 831 = (114135543711:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 831+point 2 split 4096 832)/2 = (385955253:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((385955253:ℝ)/168755200)/ClassicalSixthBranch.v ((385955253:ℝ)/168755200) = (749728856773:ℝ)/380659900776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_831
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_051
