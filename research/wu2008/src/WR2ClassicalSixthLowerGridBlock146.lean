import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints146
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_146 (j : Fin 16) : lowerPayment (16*146+j.val) ≤
    lowerValue ((point 2 split 4096 (16*146+j.val)+point 2 split 4096 (16*146+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2336 ≤ lowerValue ((point 2 split 4096 2336+point 2 split 4096 2337)/2)
    have hp : lowerPayment 2336 = (262841867264:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2336+point 2 split 4096 2337)/2 = (473639563:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473639563:ℝ)/168755200)/ClassicalSixthBranch.v ((473639563:ℝ)/168755200) = (633371777403:ℝ)/308408029336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2336
  · change lowerPayment 2337 ≤ lowerValue ((point 2 split 4096 2337+point 2 split 4096 2338)/2)
    have hp : lowerPayment 2337 = (262930425884:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2337+point 2 split 4096 2338)/2 = (18947913:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((18947913:ℝ)/6750208)/ClassicalSixthBranch.v ((18947913:ℝ)/6750208) = (633294463729:ℝ)/308360021448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2337
  · change lowerPayment 2338 ≤ lowerValue ((point 2 split 4096 2338+point 2 split 4096 2339)/2)
    have hp : lowerPayment 2338 = (263018979645:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2338+point 2 split 4096 2339)/2 = (473756087:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473756087:ℝ)/168755200)/ClassicalSixthBranch.v ((473756087:ℝ)/168755200) = (126643430011:ℝ)/61662402712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2338
  · change lowerPayment 2339 ≤ lowerValue ((point 2 split 4096 2339+point 2 split 4096 2340)/2)
    have hp : lowerPayment 2339 = (263107528563:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2339+point 2 split 4096 2340)/2 = (473814349:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473814349:ℝ)/168755200)/ClassicalSixthBranch.v ((473814349:ℝ)/168755200) = (633139836381:ℝ)/308264005672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2339
  · change lowerPayment 2340 ≤ lowerValue ((point 2 split 4096 2340+point 2 split 4096 2341)/2)
    have hp : lowerPayment 2340 = (263196072653:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2340+point 2 split 4096 2341)/2 = (473872611:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473872611:ℝ)/168755200)/ClassicalSixthBranch.v ((473872611:ℝ)/168755200) = (633062522707:ℝ)/308215997784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2340
  · change lowerPayment 2341 ≤ lowerValue ((point 2 split 4096 2341+point 2 split 4096 2342)/2)
    have hp : lowerPayment 2341 = (263284611929:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2341+point 2 split 4096 2342)/2 = (473930873:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473930873:ℝ)/168755200)/ClassicalSixthBranch.v ((473930873:ℝ)/168755200) = (632985209033:ℝ)/308167989896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2341
  · change lowerPayment 2342 ≤ lowerValue ((point 2 split 4096 2342+point 2 split 4096 2343)/2)
    have hp : lowerPayment 2342 = (263373146407:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2342+point 2 split 4096 2343)/2 = (94797827:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94797827:ℝ)/33751040)/ClassicalSixthBranch.v ((94797827:ℝ)/33751040) = (632907895359:ℝ)/308119982008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2342
  · change lowerPayment 2343 ≤ lowerValue ((point 2 split 4096 2343+point 2 split 4096 2344)/2)
    have hp : lowerPayment 2343 = (263461676101:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2343+point 2 split 4096 2344)/2 = (474047397:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474047397:ℝ)/168755200)/ClassicalSixthBranch.v ((474047397:ℝ)/168755200) = (126566116337:ℝ)/61614394824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2343
  · change lowerPayment 2344 ≤ lowerValue ((point 2 split 4096 2344+point 2 split 4096 2345)/2)
    have hp : lowerPayment 2344 = (263550201027:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2344+point 2 split 4096 2345)/2 = (474105659:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474105659:ℝ)/168755200)/ClassicalSixthBranch.v ((474105659:ℝ)/168755200) = (632753268011:ℝ)/308023966232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2344
  · change lowerPayment 2345 ≤ lowerValue ((point 2 split 4096 2345+point 2 split 4096 2346)/2)
    have hp : lowerPayment 2345 = (263638721200:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2345+point 2 split 4096 2346)/2 = (474163921:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474163921:ℝ)/168755200)/ClassicalSixthBranch.v ((474163921:ℝ)/168755200) = (632675954337:ℝ)/307975958344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2345
  · change lowerPayment 2346 ≤ lowerValue ((point 2 split 4096 2346+point 2 split 4096 2347)/2)
    have hp : lowerPayment 2346 = (263727236634:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2346+point 2 split 4096 2347)/2 = (474222183:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474222183:ℝ)/168755200)/ClassicalSixthBranch.v ((474222183:ℝ)/168755200) = (632598640663:ℝ)/307927950456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2346
  · change lowerPayment 2347 ≤ lowerValue ((point 2 split 4096 2347+point 2 split 4096 2348)/2)
    have hp : lowerPayment 2347 = (263815747346:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2347+point 2 split 4096 2348)/2 = (94856089:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94856089:ℝ)/33751040)/ClassicalSixthBranch.v ((94856089:ℝ)/33751040) = (632521326989:ℝ)/307879942568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2347
  · change lowerPayment 2348 ≤ lowerValue ((point 2 split 4096 2348+point 2 split 4096 2349)/2)
    have hp : lowerPayment 2348 = (263904253348:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2348+point 2 split 4096 2349)/2 = (474338707:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474338707:ℝ)/168755200)/ClassicalSixthBranch.v ((474338707:ℝ)/168755200) = (126488802663:ℝ)/61566386936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2348
  · change lowerPayment 2349 ≤ lowerValue ((point 2 split 4096 2349+point 2 split 4096 2350)/2)
    have hp : lowerPayment 2349 = (263992754658:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2349+point 2 split 4096 2350)/2 = (474396969:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474396969:ℝ)/168755200)/ClassicalSixthBranch.v ((474396969:ℝ)/168755200) = (632366699641:ℝ)/307783926792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2349
  · change lowerPayment 2350 ≤ lowerValue ((point 2 split 4096 2350+point 2 split 4096 2351)/2)
    have hp : lowerPayment 2350 = (264081251289:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2350+point 2 split 4096 2351)/2 = (474455231:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474455231:ℝ)/168755200)/ClassicalSixthBranch.v ((474455231:ℝ)/168755200) = (632289385967:ℝ)/307735918904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2350
  · change lowerPayment 2351 ≤ lowerValue ((point 2 split 4096 2351+point 2 split 4096 2352)/2)
    have hp : lowerPayment 2351 = (264169743257:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2351+point 2 split 4096 2352)/2 = (474513493:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((474513493:ℝ)/168755200)/ClassicalSixthBranch.v ((474513493:ℝ)/168755200) = (632212072293:ℝ)/307687911016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2351
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_146
