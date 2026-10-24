import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints192
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_192 (j : Fin 16) : upperPayment (16*192+j.val) ≤
    upperValue ((point split endpoint 4096 (16*192+j.val)+point split endpoint 4096 (16*192+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3072 ≤ upperValue ((point split endpoint 4096 3072+point split endpoint 4096 3073)/2)
    have hp : upperPayment 3072 = (152101060397:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3072+point split endpoint 4096 3073)/2 = (653424927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653424927:ℝ)/168755200)*ClassicalSixthBranch.v ((653424927:ℝ)/168755200)/ClassicalSixthBranch.r = (92583509535825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3072
  · change upperPayment 3073 ≤ upperValue ((point split endpoint 4096 3073+point split endpoint 4096 3074)/2)
    have hp : upperPayment 3073 = (151970954246:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3073+point split endpoint 4096 3074)/2 = (653450077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653450077:ℝ)/168755200)*ClassicalSixthBranch.v ((653450077:ℝ)/168755200)/ClassicalSixthBranch.r = (92563712192217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3073
  · change upperPayment 3074 ≤ upperValue ((point split endpoint 4096 3074+point split endpoint 4096 3075)/2)
    have hp : upperPayment 3074 = (151840814931:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3074+point split endpoint 4096 3075)/2 = (653475227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653475227:ℝ)/168755200)*ClassicalSixthBranch.v ((653475227:ℝ)/168755200)/ClassicalSixthBranch.r = (92543916872681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3074
  · change upperPayment 3075 ≤ upperValue ((point split endpoint 4096 3075+point split endpoint 4096 3076)/2)
    have hp : upperPayment 3075 = (151710642443:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3075+point split endpoint 4096 3076)/2 = (653500377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653500377:ℝ)/168755200)*ClassicalSixthBranch.v ((653500377:ℝ)/168755200)/ClassicalSixthBranch.r = (92524123577217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3075
  · change upperPayment 3076 ≤ upperValue ((point split endpoint 4096 3076+point split endpoint 4096 3077)/2)
    have hp : upperPayment 3076 = (151580436775:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3076+point split endpoint 4096 3077)/2 = (653525527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653525527:ℝ)/168755200)*ClassicalSixthBranch.v ((653525527:ℝ)/168755200)/ClassicalSixthBranch.r = (92504332305825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3076
  · change upperPayment 3077 ≤ upperValue ((point split endpoint 4096 3077+point split endpoint 4096 3078)/2)
    have hp : upperPayment 3077 = (151450197918:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3077+point split endpoint 4096 3078)/2 = (653550677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653550677:ℝ)/168755200)*ClassicalSixthBranch.v ((653550677:ℝ)/168755200)/ClassicalSixthBranch.r = (92484543058505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3077
  · change upperPayment 3078 ≤ upperValue ((point split endpoint 4096 3078+point split endpoint 4096 3079)/2)
    have hp : upperPayment 3078 = (151319925865:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3078+point split endpoint 4096 3079)/2 = (653575827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653575827:ℝ)/168755200)*ClassicalSixthBranch.v ((653575827:ℝ)/168755200)/ClassicalSixthBranch.r = (92464755835257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3078
  · change upperPayment 3079 ≤ upperValue ((point split endpoint 4096 3079+point split endpoint 4096 3080)/2)
    have hp : upperPayment 3079 = (151189620607:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3079+point split endpoint 4096 3080)/2 = (653600977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653600977:ℝ)/168755200)*ClassicalSixthBranch.v ((653600977:ℝ)/168755200)/ClassicalSixthBranch.r = (92444970636081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3079
  · change upperPayment 3080 ≤ upperValue ((point split endpoint 4096 3080+point split endpoint 4096 3081)/2)
    have hp : upperPayment 3080 = (151059282136:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3080+point split endpoint 4096 3081)/2 = (653626127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653626127:ℝ)/168755200)*ClassicalSixthBranch.v ((653626127:ℝ)/168755200)/ClassicalSixthBranch.r = (92425187460977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3080
  · change upperPayment 3081 ≤ upperValue ((point split endpoint 4096 3081+point split endpoint 4096 3082)/2)
    have hp : upperPayment 3081 = (150928910445:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3081+point split endpoint 4096 3082)/2 = (653651277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653651277:ℝ)/168755200)*ClassicalSixthBranch.v ((653651277:ℝ)/168755200)/ClassicalSixthBranch.r = (92405406309945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3081
  · change upperPayment 3082 ≤ upperValue ((point split endpoint 4096 3082+point split endpoint 4096 3083)/2)
    have hp : upperPayment 3082 = (150798505525:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3082+point split endpoint 4096 3083)/2 = (653676427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653676427:ℝ)/168755200)*ClassicalSixthBranch.v ((653676427:ℝ)/168755200)/ClassicalSixthBranch.r = (92385627182985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3082
  · change upperPayment 3083 ≤ upperValue ((point split endpoint 4096 3083+point split endpoint 4096 3084)/2)
    have hp : upperPayment 3083 = (150668067369:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3083+point split endpoint 4096 3084)/2 = (653701577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653701577:ℝ)/168755200)*ClassicalSixthBranch.v ((653701577:ℝ)/168755200)/ClassicalSixthBranch.r = (92365850080097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3083
  · change upperPayment 3084 ≤ upperValue ((point split endpoint 4096 3084+point split endpoint 4096 3085)/2)
    have hp : upperPayment 3084 = (150537595968:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3084+point split endpoint 4096 3085)/2 = (653726727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653726727:ℝ)/168755200)*ClassicalSixthBranch.v ((653726727:ℝ)/168755200)/ClassicalSixthBranch.r = (92346075001281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3084
  · change upperPayment 3085 ≤ upperValue ((point split endpoint 4096 3085+point split endpoint 4096 3086)/2)
    have hp : upperPayment 3085 = (150407091315:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3085+point split endpoint 4096 3086)/2 = (653751877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653751877:ℝ)/168755200)*ClassicalSixthBranch.v ((653751877:ℝ)/168755200)/ClassicalSixthBranch.r = (92326301946537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3085
  · change upperPayment 3086 ≤ upperValue ((point split endpoint 4096 3086+point split endpoint 4096 3087)/2)
    have hp : upperPayment 3086 = (150276553401:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3086+point split endpoint 4096 3087)/2 = (653777027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653777027:ℝ)/168755200)*ClassicalSixthBranch.v ((653777027:ℝ)/168755200)/ClassicalSixthBranch.r = (92306530915865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3086
  · change upperPayment 3087 ≤ upperValue ((point split endpoint 4096 3087+point split endpoint 4096 3088)/2)
    have hp : upperPayment 3087 = (150145982218:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3087+point split endpoint 4096 3088)/2 = (653802177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((653802177:ℝ)/168755200)*ClassicalSixthBranch.v ((653802177:ℝ)/168755200)/ClassicalSixthBranch.r = (92286761909265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3087
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_192
