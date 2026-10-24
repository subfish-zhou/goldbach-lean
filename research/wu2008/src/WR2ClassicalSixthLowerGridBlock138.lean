import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints138
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_138 (j : Fin 16) : lowerPayment (16*138+j.val) ≤
    lowerValue ((point 2 split 4096 (16*138+j.val)+point 2 split 4096 (16*138+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2208 ≤ lowerValue ((point 2 split 4096 2208+point 2 split 4096 2209)/2)
    have hp : lowerPayment 2208 = (251460831293:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2208+point 2 split 4096 2209)/2 = (466182027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466182027:ℝ)/168755200)/ClassicalSixthBranch.v ((466182027:ℝ)/168755200) = (25730717107:ℝ)/12582121560 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2208
  · change lowerPayment 2209 ≤ lowerValue ((point 2 split 4096 2209+point 2 split 4096 2210)/2)
    have hp : lowerPayment 2209 = (251550137253:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2209+point 2 split 4096 2210)/2 = (466240289:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466240289:ℝ)/168755200)/ClassicalSixthBranch.v ((466240289:ℝ)/168755200) = (643190614001:ℝ)/314505031112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2209
  · change lowerPayment 2210 ≤ lowerValue ((point 2 split 4096 2210+point 2 split 4096 2211)/2)
    have hp : lowerPayment 2210 = (251639436398:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2210+point 2 split 4096 2211)/2 = (466298551:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466298551:ℝ)/168755200)/ClassicalSixthBranch.v ((466298551:ℝ)/168755200) = (643113300327:ℝ)/314457023224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2210
  · change lowerPayment 2211 ≤ lowerValue ((point 2 split 4096 2211+point 2 split 4096 2212)/2)
    have hp : lowerPayment 2211 = (251728728744:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2211+point 2 split 4096 2212)/2 = (466356813:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466356813:ℝ)/168755200)/ClassicalSixthBranch.v ((466356813:ℝ)/168755200) = (643035986653:ℝ)/314409015336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2211
  · change lowerPayment 2212 ≤ lowerValue ((point 2 split 4096 2212+point 2 split 4096 2213)/2)
    have hp : lowerPayment 2212 = (251818014307:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2212+point 2 split 4096 2213)/2 = (18656603:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18656603:ℝ)/6750208)/ClassicalSixthBranch.v ((18656603:ℝ)/6750208) = (642958672979:ℝ)/314361007448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2212
  · change lowerPayment 2213 ≤ lowerValue ((point 2 split 4096 2213+point 2 split 4096 2214)/2)
    have hp : lowerPayment 2213 = (251907293101:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2213+point 2 split 4096 2214)/2 = (466473337:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466473337:ℝ)/168755200)/ClassicalSixthBranch.v ((466473337:ℝ)/168755200) = (128576271861:ℝ)/62862599912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2213
  · change lowerPayment 2214 ≤ lowerValue ((point 2 split 4096 2214+point 2 split 4096 2215)/2)
    have hp : lowerPayment 2214 = (251996565143:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2214+point 2 split 4096 2215)/2 = (4529433:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((4529433:ℝ)/1638400)/ClassicalSixthBranch.v ((4529433:ℝ)/1638400) = (6240815977:ℝ)/3051116424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2214
  · change lowerPayment 2215 ≤ lowerValue ((point 2 split 4096 2215+point 2 split 4096 2216)/2)
    have hp : lowerPayment 2215 = (252085830447:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2215+point 2 split 4096 2216)/2 = (466589861:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466589861:ℝ)/168755200)/ClassicalSixthBranch.v ((466589861:ℝ)/168755200) = (642726731957:ℝ)/314216983784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2215
  · change lowerPayment 2216 ≤ lowerValue ((point 2 split 4096 2216+point 2 split 4096 2217)/2)
    have hp : lowerPayment 2216 = (252175089031:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2216+point 2 split 4096 2217)/2 = (466648123:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466648123:ℝ)/168755200)/ClassicalSixthBranch.v ((466648123:ℝ)/168755200) = (642649418283:ℝ)/314168975896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2216
  · change lowerPayment 2217 ≤ lowerValue ((point 2 split 4096 2217+point 2 split 4096 2218)/2)
    have hp : lowerPayment 2217 = (252264340908:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2217+point 2 split 4096 2218)/2 = (93341277:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93341277:ℝ)/33751040)/ClassicalSixthBranch.v ((93341277:ℝ)/33751040) = (642572104609:ℝ)/314120968008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2217
  · change lowerPayment 2218 ≤ lowerValue ((point 2 split 4096 2218+point 2 split 4096 2219)/2)
    have hp : lowerPayment 2218 = (252353586095:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2218+point 2 split 4096 2219)/2 = (466764647:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466764647:ℝ)/168755200)/ClassicalSixthBranch.v ((466764647:ℝ)/168755200) = (128498958187:ℝ)/62814592024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2218
  · change lowerPayment 2219 ≤ lowerValue ((point 2 split 4096 2219+point 2 split 4096 2220)/2)
    have hp : lowerPayment 2219 = (252442824607:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2219+point 2 split 4096 2220)/2 = (466822909:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466822909:ℝ)/168755200)/ClassicalSixthBranch.v ((466822909:ℝ)/168755200) = (642417477261:ℝ)/314024952232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2219
  · change lowerPayment 2220 ≤ lowerValue ((point 2 split 4096 2220+point 2 split 4096 2221)/2)
    have hp : lowerPayment 2220 = (252532056460:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2220+point 2 split 4096 2221)/2 = (466881171:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466881171:ℝ)/168755200)/ClassicalSixthBranch.v ((466881171:ℝ)/168755200) = (642340163587:ℝ)/313976944344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2220
  · change lowerPayment 2221 ≤ lowerValue ((point 2 split 4096 2221+point 2 split 4096 2222)/2)
    have hp : lowerPayment 2221 = (252621281668:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2221+point 2 split 4096 2222)/2 = (466939433:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((466939433:ℝ)/168755200)/ClassicalSixthBranch.v ((466939433:ℝ)/168755200) = (642262849913:ℝ)/313928936456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2221
  · change lowerPayment 2222 ≤ lowerValue ((point 2 split 4096 2222+point 2 split 4096 2223)/2)
    have hp : lowerPayment 2222 = (252710500249:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2222+point 2 split 4096 2223)/2 = (93399539:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93399539:ℝ)/33751040)/ClassicalSixthBranch.v ((93399539:ℝ)/33751040) = (642185536239:ℝ)/313880928568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2222
  · change lowerPayment 2223 ≤ lowerValue ((point 2 split 4096 2223+point 2 split 4096 2224)/2)
    have hp : lowerPayment 2223 = (252799712217:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2223+point 2 split 4096 2224)/2 = (467055957:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((467055957:ℝ)/168755200)/ClassicalSixthBranch.v ((467055957:ℝ)/168755200) = (128421644513:ℝ)/62766584136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2223
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_138
