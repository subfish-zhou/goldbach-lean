import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints186
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_186 (j : Fin 16) : upperPayment (16*186+j.val) ≤
    upperValue ((point split endpoint 4096 (16*186+j.val)+point split endpoint 4096 (16*186+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2976 ≤ upperValue ((point split endpoint 4096 2976+point split endpoint 4096 2977)/2)
    have hp : upperPayment 2976 = (164438037055:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2976+point split endpoint 4096 2977)/2 = (651010527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651010527:ℝ)/168755200)*ClassicalSixthBranch.v ((651010527:ℝ)/168755200)/ClassicalSixthBranch.r = (94493478601425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2976
  · change upperPayment 2977 ≤ upperValue ((point split endpoint 4096 2977+point split endpoint 4096 2978)/2)
    have hp : upperPayment 2977 = (164311078069:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2977+point split endpoint 4096 2978)/2 = (651035677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651035677:ℝ)/168755200)*ClassicalSixthBranch.v ((651035677:ℝ)/168755200)/ClassicalSixthBranch.r = (94473486946905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2977
  · change upperPayment 2978 ≤ upperValue ((point split endpoint 4096 2978+point split endpoint 4096 2979)/2)
    have hp : upperPayment 2978 = (164184086669:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2978+point split endpoint 4096 2979)/2 = (651060827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651060827:ℝ)/168755200)*ClassicalSixthBranch.v ((651060827:ℝ)/168755200)/ClassicalSixthBranch.r = (94453497316457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2978
  · change upperPayment 2979 ≤ upperValue ((point split endpoint 4096 2979+point split endpoint 4096 2980)/2)
    have hp : upperPayment 2979 = (164057062847:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2979+point split endpoint 4096 2980)/2 = (651085977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651085977:ℝ)/168755200)*ClassicalSixthBranch.v ((651085977:ℝ)/168755200)/ClassicalSixthBranch.r = (94433509710081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2979
  · change upperPayment 2980 ≤ upperValue ((point split endpoint 4096 2980+point split endpoint 4096 2981)/2)
    have hp : upperPayment 2980 = (163930006596:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2980+point split endpoint 4096 2981)/2 = (651111127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651111127:ℝ)/168755200)*ClassicalSixthBranch.v ((651111127:ℝ)/168755200)/ClassicalSixthBranch.r = (94413524127777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2980
  · change upperPayment 2981 ≤ upperValue ((point split endpoint 4096 2981+point split endpoint 4096 2982)/2)
    have hp : upperPayment 2981 = (163802917908:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2981+point split endpoint 4096 2982)/2 = (651136277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651136277:ℝ)/168755200)*ClassicalSixthBranch.v ((651136277:ℝ)/168755200)/ClassicalSixthBranch.r = (94393540569545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2981
  · change upperPayment 2982 ≤ upperValue ((point split endpoint 4096 2982+point split endpoint 4096 2983)/2)
    have hp : upperPayment 2982 = (163675796775:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2982+point split endpoint 4096 2983)/2 = (651161427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651161427:ℝ)/168755200)*ClassicalSixthBranch.v ((651161427:ℝ)/168755200)/ClassicalSixthBranch.r = (94373559035385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2982
  · change upperPayment 2983 ≤ upperValue ((point split endpoint 4096 2983+point split endpoint 4096 2984)/2)
    have hp : upperPayment 2983 = (163548643190:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2983+point split endpoint 4096 2984)/2 = (651186577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651186577:ℝ)/168755200)*ClassicalSixthBranch.v ((651186577:ℝ)/168755200)/ClassicalSixthBranch.r = (94353579525297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2983
  · change upperPayment 2984 ≤ upperValue ((point split endpoint 4096 2984+point split endpoint 4096 2985)/2)
    have hp : upperPayment 2984 = (163421457145:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2984+point split endpoint 4096 2985)/2 = (651211727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651211727:ℝ)/168755200)*ClassicalSixthBranch.v ((651211727:ℝ)/168755200)/ClassicalSixthBranch.r = (94333602039281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2984
  · change upperPayment 2985 ≤ upperValue ((point split endpoint 4096 2985+point split endpoint 4096 2986)/2)
    have hp : upperPayment 2985 = (163294238632:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2985+point split endpoint 4096 2986)/2 = (651236877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651236877:ℝ)/168755200)*ClassicalSixthBranch.v ((651236877:ℝ)/168755200)/ClassicalSixthBranch.r = (94313626577337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2985
  · change upperPayment 2986 ≤ upperValue ((point split endpoint 4096 2986+point split endpoint 4096 2987)/2)
    have hp : upperPayment 2986 = (163166987643:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2986+point split endpoint 4096 2987)/2 = (651262027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651262027:ℝ)/168755200)*ClassicalSixthBranch.v ((651262027:ℝ)/168755200)/ClassicalSixthBranch.r = (94293653139465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2986
  · change upperPayment 2987 ≤ upperValue ((point split endpoint 4096 2987+point split endpoint 4096 2988)/2)
    have hp : upperPayment 2987 = (163039704172:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2987+point split endpoint 4096 2988)/2 = (651287177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651287177:ℝ)/168755200)*ClassicalSixthBranch.v ((651287177:ℝ)/168755200)/ClassicalSixthBranch.r = (94273681725665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2987
  · change upperPayment 2988 ≤ upperValue ((point split endpoint 4096 2988+point split endpoint 4096 2989)/2)
    have hp : upperPayment 2988 = (162912388210:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2988+point split endpoint 4096 2989)/2 = (651312327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651312327:ℝ)/168755200)*ClassicalSixthBranch.v ((651312327:ℝ)/168755200)/ClassicalSixthBranch.r = (94253712335937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2988
  · change upperPayment 2989 ≤ upperValue ((point split endpoint 4096 2989+point split endpoint 4096 2990)/2)
    have hp : upperPayment 2989 = (162785039749:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2989+point split endpoint 4096 2990)/2 = (651337477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651337477:ℝ)/168755200)*ClassicalSixthBranch.v ((651337477:ℝ)/168755200)/ClassicalSixthBranch.r = (94233744970281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2989
  · change upperPayment 2990 ≤ upperValue ((point split endpoint 4096 2990+point split endpoint 4096 2991)/2)
    have hp : upperPayment 2990 = (162657658782:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2990+point split endpoint 4096 2991)/2 = (6323909:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6323909:ℝ)/1638400)*ClassicalSixthBranch.v ((6323909:ℝ)/1638400)/ClassicalSixthBranch.r = (914696889599:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2990
  · change upperPayment 2991 ≤ upperValue ((point split endpoint 4096 2991+point split endpoint 4096 2992)/2)
    have hp : upperPayment 2991 = (162530245301:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2991+point split endpoint 4096 2992)/2 = (651387777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((651387777:ℝ)/168755200)*ClassicalSixthBranch.v ((651387777:ℝ)/168755200)/ClassicalSixthBranch.r = (94193816311185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2991
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_186
