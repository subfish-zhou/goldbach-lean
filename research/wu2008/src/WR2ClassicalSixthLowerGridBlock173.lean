import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints173
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_173 (j : Fin 16) : lowerPayment (16*173+j.val) ≤
    lowerValue ((point 2 split 4096 (16*173+j.val)+point 2 split 4096 (16*173+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2768 ≤ lowerValue ((point 2 split 4096 2768+point 2 split 4096 2769)/2)
    have hp : lowerPayment 2768 = (300843136954:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2768+point 2 split 4096 2769)/2 = (498808747:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498808747:ℝ)/168755200)/ClassicalSixthBranch.v ((498808747:ℝ)/168755200) = (119994454047:ℝ)/57533724344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2768
  · change lowerPayment 2769 ≤ lowerValue ((point 2 split 4096 2769+point 2 split 4096 2770)/2)
    have hp : lowerPayment 2769 = (300930957910:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2769+point 2 split 4096 2770)/2 = (498867009:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498867009:ℝ)/168755200)/ClassicalSixthBranch.v ((498867009:ℝ)/168755200) = (599894956561:ℝ)/287620613832 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2769
  · change lowerPayment 2770 ≤ lowerValue ((point 2 split 4096 2770+point 2 split 4096 2771)/2)
    have hp : lowerPayment 2770 = (301018780259:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2770+point 2 split 4096 2771)/2 = (498925271:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498925271:ℝ)/168755200)/ClassicalSixthBranch.v ((498925271:ℝ)/168755200) = (599817642887:ℝ)/287572605944 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2770
  · change lowerPayment 2771 ≤ lowerValue ((point 2 split 4096 2771+point 2 split 4096 2772)/2)
    have hp : lowerPayment 2771 = (301106604015:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2771+point 2 split 4096 2772)/2 = (498983533:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((498983533:ℝ)/168755200)/ClassicalSixthBranch.v ((498983533:ℝ)/168755200) = (599740329213:ℝ)/287524598056 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2771
  · change lowerPayment 2772 ≤ lowerValue ((point 2 split 4096 2772+point 2 split 4096 2773)/2)
    have hp : lowerPayment 2772 = (301194429193:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2772+point 2 split 4096 2773)/2 = (99808359:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99808359:ℝ)/33751040)/ClassicalSixthBranch.v ((99808359:ℝ)/33751040) = (599663015539:ℝ)/287476590168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2772
  · change lowerPayment 2773 ≤ lowerValue ((point 2 split 4096 2773+point 2 split 4096 2774)/2)
    have hp : lowerPayment 2773 = (301282255807:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2773+point 2 split 4096 2774)/2 = (499100057:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499100057:ℝ)/168755200)/ClassicalSixthBranch.v ((499100057:ℝ)/168755200) = (119917140373:ℝ)/57485716456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2773
  · change lowerPayment 2774 ≤ lowerValue ((point 2 split 4096 2774+point 2 split 4096 2775)/2)
    have hp : lowerPayment 2774 = (301370083870:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2774+point 2 split 4096 2775)/2 = (499158319:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499158319:ℝ)/168755200)/ClassicalSixthBranch.v ((499158319:ℝ)/168755200) = (599508388191:ℝ)/287380574392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2774
  · change lowerPayment 2775 ≤ lowerValue ((point 2 split 4096 2775+point 2 split 4096 2776)/2)
    have hp : lowerPayment 2775 = (301457913397:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2775+point 2 split 4096 2776)/2 = (499216581:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499216581:ℝ)/168755200)/ClassicalSixthBranch.v ((499216581:ℝ)/168755200) = (599431074517:ℝ)/287332566504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2775
  · change lowerPayment 2776 ≤ lowerValue ((point 2 split 4096 2776+point 2 split 4096 2777)/2)
    have hp : lowerPayment 2776 = (301545744403:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2776+point 2 split 4096 2777)/2 = (499274843:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499274843:ℝ)/168755200)/ClassicalSixthBranch.v ((499274843:ℝ)/168755200) = (599353760843:ℝ)/287284558616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2776
  · change lowerPayment 2777 ≤ lowerValue ((point 2 split 4096 2777+point 2 split 4096 2778)/2)
    have hp : lowerPayment 2777 = (301633576901:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2777+point 2 split 4096 2778)/2 = (99866621:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99866621:ℝ)/33751040)/ClassicalSixthBranch.v ((99866621:ℝ)/33751040) = (599276447169:ℝ)/287236550728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2777
  · change lowerPayment 2778 ≤ lowerValue ((point 2 split 4096 2778+point 2 split 4096 2779)/2)
    have hp : lowerPayment 2778 = (301721410905:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2778+point 2 split 4096 2779)/2 = (499391367:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499391367:ℝ)/168755200)/ClassicalSixthBranch.v ((499391367:ℝ)/168755200) = (119839826699:ℝ)/57437708568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2778
  · change lowerPayment 2779 ≤ lowerValue ((point 2 split 4096 2779+point 2 split 4096 2780)/2)
    have hp : lowerPayment 2779 = (301809246429:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2779+point 2 split 4096 2780)/2 = (499449629:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499449629:ℝ)/168755200)/ClassicalSixthBranch.v ((499449629:ℝ)/168755200) = (599121819821:ℝ)/287140534952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2779
  · change lowerPayment 2780 ≤ lowerValue ((point 2 split 4096 2780+point 2 split 4096 2781)/2)
    have hp : lowerPayment 2780 = (301897083488:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2780+point 2 split 4096 2781)/2 = (499507891:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499507891:ℝ)/168755200)/ClassicalSixthBranch.v ((499507891:ℝ)/168755200) = (599044506147:ℝ)/287092527064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2780
  · change lowerPayment 2781 ≤ lowerValue ((point 2 split 4096 2781+point 2 split 4096 2782)/2)
    have hp : lowerPayment 2781 = (301984922096:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2781+point 2 split 4096 2782)/2 = (499566153:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499566153:ℝ)/168755200)/ClassicalSixthBranch.v ((499566153:ℝ)/168755200) = (598967192473:ℝ)/287044519176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2781
  · change lowerPayment 2782 ≤ lowerValue ((point 2 split 4096 2782+point 2 split 4096 2783)/2)
    have hp : lowerPayment 2782 = (302072762267:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2782+point 2 split 4096 2783)/2 = (99924883:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((99924883:ℝ)/33751040)/ClassicalSixthBranch.v ((99924883:ℝ)/33751040) = (598889878799:ℝ)/286996511288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2782
  · change lowerPayment 2783 ≤ lowerValue ((point 2 split 4096 2783+point 2 split 4096 2784)/2)
    have hp : lowerPayment 2783 = (302160604014:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2783+point 2 split 4096 2784)/2 = (499682677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((499682677:ℝ)/168755200)/ClassicalSixthBranch.v ((499682677:ℝ)/168755200) = (23952502605:ℝ)/11477940136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2783
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_173
