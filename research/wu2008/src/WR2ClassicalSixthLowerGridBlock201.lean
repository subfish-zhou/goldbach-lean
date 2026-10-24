import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints201
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_201 (j : Fin 16) : lowerPayment (16*201+j.val) ≤
    lowerValue ((point 2 split 4096 (16*201+j.val)+point 2 split 4096 (16*201+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3216 ≤ lowerValue ((point 2 split 4096 3216+point 2 split 4096 3217)/2)
    have hp : lowerPayment 3216 = (340536783600:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3216+point 2 split 4096 3217)/2 = (524910123:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((524910123:ℝ)/168755200)/ClassicalSixthBranch.v ((524910123:ℝ)/168755200) = (565335744283:ℝ)/266161087896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3216
  · change lowerPayment 3217 ≤ lowerValue ((point 2 split 4096 3217+point 2 split 4096 3218)/2)
    have hp : lowerPayment 3217 = (340626645901:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3217+point 2 split 4096 3218)/2 = (104993677:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((104993677:ℝ)/33751040)/ClassicalSixthBranch.v ((104993677:ℝ)/33751040) = (565258430609:ℝ)/266113080008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3217
  · change lowerPayment 3218 ≤ lowerValue ((point 2 split 4096 3218+point 2 split 4096 3219)/2)
    have hp : lowerPayment 3218 = (340716515966:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3218+point 2 split 4096 3219)/2 = (525026647:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525026647:ℝ)/168755200)/ClassicalSixthBranch.v ((525026647:ℝ)/168755200) = (113036223387:ℝ)/53213014424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3218
  · change lowerPayment 3219 ≤ lowerValue ((point 2 split 4096 3219+point 2 split 4096 3220)/2)
    have hp : lowerPayment 3219 = (340806393809:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3219+point 2 split 4096 3220)/2 = (525084909:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525084909:ℝ)/168755200)/ClassicalSixthBranch.v ((525084909:ℝ)/168755200) = (565103803261:ℝ)/266017064232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3219
  · change lowerPayment 3220 ≤ lowerValue ((point 2 split 4096 3220+point 2 split 4096 3221)/2)
    have hp : lowerPayment 3220 = (340896279446:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3220+point 2 split 4096 3221)/2 = (525143171:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525143171:ℝ)/168755200)/ClassicalSixthBranch.v ((525143171:ℝ)/168755200) = (565026489587:ℝ)/265969056344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3220
  · change lowerPayment 3221 ≤ lowerValue ((point 2 split 4096 3221+point 2 split 4096 3222)/2)
    have hp : lowerPayment 3221 = (340986172891:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3221+point 2 split 4096 3222)/2 = (525201433:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525201433:ℝ)/168755200)/ClassicalSixthBranch.v ((525201433:ℝ)/168755200) = (564949175913:ℝ)/265921048456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3221
  · change lowerPayment 3222 ≤ lowerValue ((point 2 split 4096 3222+point 2 split 4096 3223)/2)
    have hp : lowerPayment 3222 = (341076074158:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3222+point 2 split 4096 3223)/2 = (105051939:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105051939:ℝ)/33751040)/ClassicalSixthBranch.v ((105051939:ℝ)/33751040) = (564871862239:ℝ)/265873040568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3222
  · change lowerPayment 3223 ≤ lowerValue ((point 2 split 4096 3223+point 2 split 4096 3224)/2)
    have hp : lowerPayment 3223 = (341165983261:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3223+point 2 split 4096 3224)/2 = (525317957:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525317957:ℝ)/168755200)/ClassicalSixthBranch.v ((525317957:ℝ)/168755200) = (112958909713:ℝ)/53165006536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3223
  · change lowerPayment 3224 ≤ lowerValue ((point 2 split 4096 3224+point 2 split 4096 3225)/2)
    have hp : lowerPayment 3224 = (341255900216:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3224+point 2 split 4096 3225)/2 = (525376219:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525376219:ℝ)/168755200)/ClassicalSixthBranch.v ((525376219:ℝ)/168755200) = (564717234891:ℝ)/265777024792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3224
  · change lowerPayment 3225 ≤ lowerValue ((point 2 split 4096 3225+point 2 split 4096 3226)/2)
    have hp : lowerPayment 3225 = (341345825037:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3225+point 2 split 4096 3226)/2 = (525434481:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525434481:ℝ)/168755200)/ClassicalSixthBranch.v ((525434481:ℝ)/168755200) = (564639921217:ℝ)/265729016904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3225
  · change lowerPayment 3226 ≤ lowerValue ((point 2 split 4096 3226+point 2 split 4096 3227)/2)
    have hp : lowerPayment 3226 = (341435757739:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3226+point 2 split 4096 3227)/2 = (525492743:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525492743:ℝ)/168755200)/ClassicalSixthBranch.v ((525492743:ℝ)/168755200) = (564562607543:ℝ)/265681009016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3226
  · change lowerPayment 3227 ≤ lowerValue ((point 2 split 4096 3227+point 2 split 4096 3228)/2)
    have hp : lowerPayment 3227 = (341525698336:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3227+point 2 split 4096 3228)/2 = (105110201:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((105110201:ℝ)/33751040)/ClassicalSixthBranch.v ((105110201:ℝ)/33751040) = (564485293869:ℝ)/265633001128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3227
  · change lowerPayment 3228 ≤ lowerValue ((point 2 split 4096 3228+point 2 split 4096 3229)/2)
    have hp : lowerPayment 3228 = (341615646842:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3228+point 2 split 4096 3229)/2 = (525609267:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525609267:ℝ)/168755200)/ClassicalSixthBranch.v ((525609267:ℝ)/168755200) = (112881596039:ℝ)/53116998648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3228
  · change lowerPayment 3229 ≤ lowerValue ((point 2 split 4096 3229+point 2 split 4096 3230)/2)
    have hp : lowerPayment 3229 = (341705603272:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3229+point 2 split 4096 3230)/2 = (525667529:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525667529:ℝ)/168755200)/ClassicalSixthBranch.v ((525667529:ℝ)/168755200) = (564330666521:ℝ)/265536985352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3229
  · change lowerPayment 3230 ≤ lowerValue ((point 2 split 4096 3230+point 2 split 4096 3231)/2)
    have hp : lowerPayment 3230 = (341795567641:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3230+point 2 split 4096 3231)/2 = (525725791:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525725791:ℝ)/168755200)/ClassicalSixthBranch.v ((525725791:ℝ)/168755200) = (564253352847:ℝ)/265488977464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3230
  · change lowerPayment 3231 ≤ lowerValue ((point 2 split 4096 3231+point 2 split 4096 3232)/2)
    have hp : lowerPayment 3231 = (341885539963:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3231+point 2 split 4096 3232)/2 = (525784053:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((525784053:ℝ)/168755200)/ClassicalSixthBranch.v ((525784053:ℝ)/168755200) = (564176039173:ℝ)/265440969576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3231
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_201
