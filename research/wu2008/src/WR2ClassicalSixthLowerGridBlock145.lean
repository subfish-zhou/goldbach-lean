import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints145
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_145 (j : Fin 16) : lowerPayment (16*145+j.val) ≤
    lowerValue ((point 2 split 4096 (16*145+j.val)+point 2 split 4096 (16*145+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2320 ≤ lowerValue ((point 2 split 4096 2320+point 2 split 4096 2321)/2)
    have hp : lowerPayment 2320 = (261424256322:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2320+point 2 split 4096 2321)/2 = (472707371:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472707371:ℝ)/168755200)/ClassicalSixthBranch.v ((472707371:ℝ)/168755200) = (634608796187:ℝ)/309176155544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2320
  · change lowerPayment 2321 ≤ lowerValue ((point 2 split 4096 2321+point 2 split 4096 2322)/2)
    have hp : lowerPayment 2321 = (261512894723:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2321+point 2 split 4096 2322)/2 = (472765633:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472765633:ℝ)/168755200)/ClassicalSixthBranch.v ((472765633:ℝ)/168755200) = (634531482513:ℝ)/309128147656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2321
  · change lowerPayment 2322 ≤ lowerValue ((point 2 split 4096 2322+point 2 split 4096 2323)/2)
    have hp : lowerPayment 2322 = (261601528026:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2322+point 2 split 4096 2323)/2 = (94564779:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94564779:ℝ)/33751040)/ClassicalSixthBranch.v ((94564779:ℝ)/33751040) = (634454168839:ℝ)/309080139768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2322
  · change lowerPayment 2323 ≤ lowerValue ((point 2 split 4096 2323+point 2 split 4096 2324)/2)
    have hp : lowerPayment 2323 = (261690156244:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2323+point 2 split 4096 2324)/2 = (472882157:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472882157:ℝ)/168755200)/ClassicalSixthBranch.v ((472882157:ℝ)/168755200) = (126875371033:ℝ)/61806426376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2323
  · change lowerPayment 2324 ≤ lowerValue ((point 2 split 4096 2324+point 2 split 4096 2325)/2)
    have hp : lowerPayment 2324 = (261778779393:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2324+point 2 split 4096 2325)/2 = (472940419:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472940419:ℝ)/168755200)/ClassicalSixthBranch.v ((472940419:ℝ)/168755200) = (634299541491:ℝ)/308984123992 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2324
  · change lowerPayment 2325 ≤ lowerValue ((point 2 split 4096 2325+point 2 split 4096 2326)/2)
    have hp : lowerPayment 2325 = (261867397487:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2325+point 2 split 4096 2326)/2 = (472998681:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((472998681:ℝ)/168755200)/ClassicalSixthBranch.v ((472998681:ℝ)/168755200) = (634222227817:ℝ)/308936116104 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2325
  · change lowerPayment 2326 ≤ lowerValue ((point 2 split 4096 2326+point 2 split 4096 2327)/2)
    have hp : lowerPayment 2326 = (261956010543:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2326+point 2 split 4096 2327)/2 = (473056943:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473056943:ℝ)/168755200)/ClassicalSixthBranch.v ((473056943:ℝ)/168755200) = (634144914143:ℝ)/308888108216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2326
  · change lowerPayment 2327 ≤ lowerValue ((point 2 split 4096 2327+point 2 split 4096 2328)/2)
    have hp : lowerPayment 2327 = (262044618574:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2327+point 2 split 4096 2328)/2 = (94623041:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94623041:ℝ)/33751040)/ClassicalSixthBranch.v ((94623041:ℝ)/33751040) = (634067600469:ℝ)/308840100328 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2327
  · change lowerPayment 2328 ≤ lowerValue ((point 2 split 4096 2328+point 2 split 4096 2329)/2)
    have hp : lowerPayment 2328 = (262133221597:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2328+point 2 split 4096 2329)/2 = (473173467:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473173467:ℝ)/168755200)/ClassicalSixthBranch.v ((473173467:ℝ)/168755200) = (126798057359:ℝ)/61758418488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2328
  · change lowerPayment 2329 ≤ lowerValue ((point 2 split 4096 2329+point 2 split 4096 2330)/2)
    have hp : lowerPayment 2329 = (262221819626:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2329+point 2 split 4096 2330)/2 = (473231729:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473231729:ℝ)/168755200)/ClassicalSixthBranch.v ((473231729:ℝ)/168755200) = (633912973121:ℝ)/308744084552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2329
  · change lowerPayment 2330 ≤ lowerValue ((point 2 split 4096 2330+point 2 split 4096 2331)/2)
    have hp : lowerPayment 2330 = (262310412676:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2330+point 2 split 4096 2331)/2 = (473289991:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473289991:ℝ)/168755200)/ClassicalSixthBranch.v ((473289991:ℝ)/168755200) = (633835659447:ℝ)/308696076664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2330
  · change lowerPayment 2331 ≤ lowerValue ((point 2 split 4096 2331+point 2 split 4096 2332)/2)
    have hp : lowerPayment 2331 = (262399000762:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2331+point 2 split 4096 2332)/2 = (473348253:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473348253:ℝ)/168755200)/ClassicalSixthBranch.v ((473348253:ℝ)/168755200) = (633758345773:ℝ)/308648068776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2331
  · change lowerPayment 2332 ≤ lowerValue ((point 2 split 4096 2332+point 2 split 4096 2333)/2)
    have hp : lowerPayment 2332 = (262487583900:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2332+point 2 split 4096 2333)/2 = (94681303:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94681303:ℝ)/33751040)/ClassicalSixthBranch.v ((94681303:ℝ)/33751040) = (633681032099:ℝ)/308600060888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2332
  · change lowerPayment 2333 ≤ lowerValue ((point 2 split 4096 2333+point 2 split 4096 2334)/2)
    have hp : lowerPayment 2333 = (262576162104:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2333+point 2 split 4096 2334)/2 = (473464777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473464777:ℝ)/168755200)/ClassicalSixthBranch.v ((473464777:ℝ)/168755200) = (25344148737:ℝ)/12342082120 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2333
  · change lowerPayment 2334 ≤ lowerValue ((point 2 split 4096 2334+point 2 split 4096 2335)/2)
    have hp : lowerPayment 2334 = (262664735389:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2334+point 2 split 4096 2335)/2 = (473523039:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473523039:ℝ)/168755200)/ClassicalSixthBranch.v ((473523039:ℝ)/168755200) = (633526404751:ℝ)/308504045112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2334
  · change lowerPayment 2335 ≤ lowerValue ((point 2 split 4096 2335+point 2 split 4096 2336)/2)
    have hp : lowerPayment 2335 = (262753303771:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2335+point 2 split 4096 2336)/2 = (473581301:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((473581301:ℝ)/168755200)/ClassicalSixthBranch.v ((473581301:ℝ)/168755200) = (633449091077:ℝ)/308456037224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2335
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_145
