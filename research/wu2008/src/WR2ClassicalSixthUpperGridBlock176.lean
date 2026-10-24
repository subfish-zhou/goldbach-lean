import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints176
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_176 (j : Fin 16) : upperPayment (16*176+j.val) ≤
    upperValue ((point split endpoint 4096 (16*176+j.val)+point split endpoint 4096 (16*176+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2816 ≤ upperValue ((point split endpoint 4096 2816+point split endpoint 4096 2817)/2)
    have hp : upperPayment 2816 = (184339230312:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2816+point split endpoint 4096 2817)/2 = (646986527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((646986527:ℝ)/168755200)*ClassicalSixthBranch.v ((646986527:ℝ)/168755200)/ClassicalSixthBranch.r = (97718213371985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2816
  · change upperPayment 2817 ≤ upperValue ((point split endpoint 4096 2817+point split endpoint 4096 2818)/2)
    have hp : upperPayment 2817 = (184217360902:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2817+point split endpoint 4096 2818)/2 = (647011677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647011677:ℝ)/168755200)*ClassicalSixthBranch.v ((647011677:ℝ)/168755200)/ClassicalSixthBranch.r = (97697897865945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2817
  · change upperPayment 2818 ≤ upperValue ((point split endpoint 4096 2818+point split endpoint 4096 2819)/2)
    have hp : upperPayment 2818 = (184095460267:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2818+point split endpoint 4096 2819)/2 = (647036827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647036827:ℝ)/168755200)*ClassicalSixthBranch.v ((647036827:ℝ)/168755200)/ClassicalSixthBranch.r = (97677584383977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2818
  · change upperPayment 2819 ≤ upperValue ((point split endpoint 4096 2819+point split endpoint 4096 2820)/2)
    have hp : upperPayment 2819 = (183973528398:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2819+point split endpoint 4096 2820)/2 = (647061977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647061977:ℝ)/168755200)*ClassicalSixthBranch.v ((647061977:ℝ)/168755200)/ClassicalSixthBranch.r = (97657272926081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2819
  · change upperPayment 2820 ≤ upperValue ((point split endpoint 4096 2820+point split endpoint 4096 2821)/2)
    have hp : upperPayment 2820 = (183851565289:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2820+point split endpoint 4096 2821)/2 = (647087127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647087127:ℝ)/168755200)*ClassicalSixthBranch.v ((647087127:ℝ)/168755200)/ClassicalSixthBranch.r = (97636963492257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2820
  · change upperPayment 2821 ≤ upperValue ((point split endpoint 4096 2821+point split endpoint 4096 2822)/2)
    have hp : upperPayment 2821 = (183729570933:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2821+point split endpoint 4096 2822)/2 = (647112277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647112277:ℝ)/168755200)*ClassicalSixthBranch.v ((647112277:ℝ)/168755200)/ClassicalSixthBranch.r = (97616656082505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2821
  · change upperPayment 2822 ≤ upperValue ((point split endpoint 4096 2822+point split endpoint 4096 2823)/2)
    have hp : upperPayment 2822 = (183607545322:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2822+point split endpoint 4096 2823)/2 = (647137427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647137427:ℝ)/168755200)*ClassicalSixthBranch.v ((647137427:ℝ)/168755200)/ClassicalSixthBranch.r = (97596350696825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2822
  · change upperPayment 2823 ≤ upperValue ((point split endpoint 4096 2823+point split endpoint 4096 2824)/2)
    have hp : upperPayment 2823 = (183485488449:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2823+point split endpoint 4096 2824)/2 = (647162577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647162577:ℝ)/168755200)*ClassicalSixthBranch.v ((647162577:ℝ)/168755200)/ClassicalSixthBranch.r = (97576047335217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2823
  · change upperPayment 2824 ≤ upperValue ((point split endpoint 4096 2824+point split endpoint 4096 2825)/2)
    have hp : upperPayment 2824 = (183363400306:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2824+point split endpoint 4096 2825)/2 = (647187727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647187727:ℝ)/168755200)*ClassicalSixthBranch.v ((647187727:ℝ)/168755200)/ClassicalSixthBranch.r = (97555745997681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2824
  · change upperPayment 2825 ≤ upperValue ((point split endpoint 4096 2825+point split endpoint 4096 2826)/2)
    have hp : upperPayment 2825 = (183241280888:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2825+point split endpoint 4096 2826)/2 = (647212877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647212877:ℝ)/168755200)*ClassicalSixthBranch.v ((647212877:ℝ)/168755200)/ClassicalSixthBranch.r = (97535446684217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2825
  · change upperPayment 2826 ≤ upperValue ((point split endpoint 4096 2826+point split endpoint 4096 2827)/2)
    have hp : upperPayment 2826 = (183119130185:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2826+point split endpoint 4096 2827)/2 = (647238027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647238027:ℝ)/168755200)*ClassicalSixthBranch.v ((647238027:ℝ)/168755200)/ClassicalSixthBranch.r = (97515149394825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2826
  · change upperPayment 2827 ≤ upperValue ((point split endpoint 4096 2827+point split endpoint 4096 2828)/2)
    have hp : upperPayment 2827 = (182996948192:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2827+point split endpoint 4096 2828)/2 = (647263177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647263177:ℝ)/168755200)*ClassicalSixthBranch.v ((647263177:ℝ)/168755200)/ClassicalSixthBranch.r = (97494854129505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2827
  · change upperPayment 2828 ≤ upperValue ((point split endpoint 4096 2828+point split endpoint 4096 2829)/2)
    have hp : upperPayment 2828 = (182874734901:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2828+point split endpoint 4096 2829)/2 = (647288327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647288327:ℝ)/168755200)*ClassicalSixthBranch.v ((647288327:ℝ)/168755200)/ClassicalSixthBranch.r = (97474560888257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2828
  · change upperPayment 2829 ≤ upperValue ((point split endpoint 4096 2829+point split endpoint 4096 2830)/2)
    have hp : upperPayment 2829 = (182752490305:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2829+point split endpoint 4096 2830)/2 = (647313477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647313477:ℝ)/168755200)*ClassicalSixthBranch.v ((647313477:ℝ)/168755200)/ClassicalSixthBranch.r = (97454269671081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2829
  · change upperPayment 2830 ≤ upperValue ((point split endpoint 4096 2830+point split endpoint 4096 2831)/2)
    have hp : upperPayment 2830 = (182630214397:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2830+point split endpoint 4096 2831)/2 = (647338627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647338627:ℝ)/168755200)*ClassicalSixthBranch.v ((647338627:ℝ)/168755200)/ClassicalSixthBranch.r = (97433980477977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2830
  · change upperPayment 2831 ≤ upperValue ((point split endpoint 4096 2831+point split endpoint 4096 2832)/2)
    have hp : upperPayment 2831 = (182507907168:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2831+point split endpoint 4096 2832)/2 = (647363777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((647363777:ℝ)/168755200)*ClassicalSixthBranch.v ((647363777:ℝ)/168755200)/ClassicalSixthBranch.r = (97413693308945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2831
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_176
