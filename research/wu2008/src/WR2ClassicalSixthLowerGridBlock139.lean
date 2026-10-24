import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints139
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_139 (j : Fin 16) : lowerPayment (16*139+j.val) ≤
    lowerValue ((point 2 split 4096 (16*139+j.val)+point 2 split 4096 (16*139+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2224 ≤ lowerValue ((point 2 split 4096 2224+point 2 split 4096 2225)/2)
    have hp : lowerPayment 2224 = (252888917587:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2224+point 2 split 4096 2225)/2 = (467114219:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467114219:ℝ)/168755200)/ClassicalSixthBranch.v ((467114219:ℝ)/168755200) = (642030908891:ℝ)/313784912792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2224
  · change lowerPayment 2225 ≤ lowerValue ((point 2 split 4096 2225+point 2 split 4096 2226)/2)
    have hp : lowerPayment 2225 = (252978116375:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2225+point 2 split 4096 2226)/2 = (467172481:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467172481:ℝ)/168755200)/ClassicalSixthBranch.v ((467172481:ℝ)/168755200) = (641953595217:ℝ)/313736904904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2225
  · change lowerPayment 2226 ≤ lowerValue ((point 2 split 4096 2226+point 2 split 4096 2227)/2)
    have hp : lowerPayment 2226 = (253067308597:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2226+point 2 split 4096 2227)/2 = (467230743:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467230743:ℝ)/168755200)/ClassicalSixthBranch.v ((467230743:ℝ)/168755200) = (641876281543:ℝ)/313688897016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2226
  · change lowerPayment 2227 ≤ lowerValue ((point 2 split 4096 2227+point 2 split 4096 2228)/2)
    have hp : lowerPayment 2227 = (253156494268:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2227+point 2 split 4096 2228)/2 = (93457801:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93457801:ℝ)/33751040)/ClassicalSixthBranch.v ((93457801:ℝ)/33751040) = (641798967869:ℝ)/313640889128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2227
  · change lowerPayment 2228 ≤ lowerValue ((point 2 split 4096 2228+point 2 split 4096 2229)/2)
    have hp : lowerPayment 2228 = (253245673404:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2228+point 2 split 4096 2229)/2 = (467347267:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467347267:ℝ)/168755200)/ClassicalSixthBranch.v ((467347267:ℝ)/168755200) = (128344330839:ℝ)/62718576248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2228
  · change lowerPayment 2229 ≤ lowerValue ((point 2 split 4096 2229+point 2 split 4096 2230)/2)
    have hp : lowerPayment 2229 = (253334846020:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2229+point 2 split 4096 2230)/2 = (467405529:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467405529:ℝ)/168755200)/ClassicalSixthBranch.v ((467405529:ℝ)/168755200) = (641644340521:ℝ)/313544873352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2229
  · change lowerPayment 2230 ≤ lowerValue ((point 2 split 4096 2230+point 2 split 4096 2231)/2)
    have hp : lowerPayment 2230 = (253424012131:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2230+point 2 split 4096 2231)/2 = (467463791:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467463791:ℝ)/168755200)/ClassicalSixthBranch.v ((467463791:ℝ)/168755200) = (641567026847:ℝ)/313496865464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2230
  · change lowerPayment 2231 ≤ lowerValue ((point 2 split 4096 2231+point 2 split 4096 2232)/2)
    have hp : lowerPayment 2231 = (253513171753:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2231+point 2 split 4096 2232)/2 = (467522053:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467522053:ℝ)/168755200)/ClassicalSixthBranch.v ((467522053:ℝ)/168755200) = (641489713173:ℝ)/313448857576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2231
  · change lowerPayment 2232 ≤ lowerValue ((point 2 split 4096 2232+point 2 split 4096 2233)/2)
    have hp : lowerPayment 2232 = (253602324902:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2232+point 2 split 4096 2233)/2 = (93516063:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93516063:ℝ)/33751040)/ClassicalSixthBranch.v ((93516063:ℝ)/33751040) = (641412399499:ℝ)/313400849688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2232
  · change lowerPayment 2233 ≤ lowerValue ((point 2 split 4096 2233+point 2 split 4096 2234)/2)
    have hp : lowerPayment 2233 = (253691471592:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2233+point 2 split 4096 2234)/2 = (467638577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467638577:ℝ)/168755200)/ClassicalSixthBranch.v ((467638577:ℝ)/168755200) = (25653403433:ℝ)/12534113672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2233
  · change lowerPayment 2234 ≤ lowerValue ((point 2 split 4096 2234+point 2 split 4096 2235)/2)
    have hp : lowerPayment 2234 = (253780611840:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2234+point 2 split 4096 2235)/2 = (467696839:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467696839:ℝ)/168755200)/ClassicalSixthBranch.v ((467696839:ℝ)/168755200) = (641257772151:ℝ)/313304833912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2234
  · change lowerPayment 2235 ≤ lowerValue ((point 2 split 4096 2235+point 2 split 4096 2236)/2)
    have hp : lowerPayment 2235 = (253869745661:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2235+point 2 split 4096 2236)/2 = (467755101:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467755101:ℝ)/168755200)/ClassicalSixthBranch.v ((467755101:ℝ)/168755200) = (641180458477:ℝ)/313256826024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2235
  · change lowerPayment 2236 ≤ lowerValue ((point 2 split 4096 2236+point 2 split 4096 2237)/2)
    have hp : lowerPayment 2236 = (253958873070:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2236+point 2 split 4096 2237)/2 = (467813363:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467813363:ℝ)/168755200)/ClassicalSixthBranch.v ((467813363:ℝ)/168755200) = (641103144803:ℝ)/313208818136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2236
  · change lowerPayment 2237 ≤ lowerValue ((point 2 split 4096 2237+point 2 split 4096 2238)/2)
    have hp : lowerPayment 2237 = (254047994083:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2237+point 2 split 4096 2238)/2 = (18714865:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18714865:ℝ)/6750208)/ClassicalSixthBranch.v ((18714865:ℝ)/6750208) = (641025831129:ℝ)/313160810248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2237
  · change lowerPayment 2238 ≤ lowerValue ((point 2 split 4096 2238+point 2 split 4096 2239)/2)
    have hp : lowerPayment 2238 = (254137108715:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2238+point 2 split 4096 2239)/2 = (467929887:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467929887:ℝ)/168755200)/ClassicalSixthBranch.v ((467929887:ℝ)/168755200) = (128189703491:ℝ)/62622560472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2238
  · change lowerPayment 2239 ≤ lowerValue ((point 2 split 4096 2239+point 2 split 4096 2240)/2)
    have hp : lowerPayment 2239 = (254226216981:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2239+point 2 split 4096 2240)/2 = (467988149:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467988149:ℝ)/168755200)/ClassicalSixthBranch.v ((467988149:ℝ)/168755200) = (640871203781:ℝ)/313064794472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2239
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_139
