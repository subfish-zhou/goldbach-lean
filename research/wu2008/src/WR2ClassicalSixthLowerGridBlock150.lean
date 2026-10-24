import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints150
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_150 (j : Fin 16) : lowerPayment (16*150+j.val) ≤
    lowerValue ((point 2 split 4096 (16*150+j.val)+point 2 split 4096 (16*150+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2400 ≤ lowerValue ((point 2 split 4096 2400+point 2 split 4096 2401)/2)
    have hp : lowerPayment 2400 = (268500448188:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2400+point 2 split 4096 2401)/2 = (477368331:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477368331:ℝ)/168755200)/ClassicalSixthBranch.v ((477368331:ℝ)/168755200) = (628423702267:ℝ)/305335524504 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2400
  · change lowerPayment 2401 ≤ lowerValue ((point 2 split 4096 2401+point 2 split 4096 2402)/2)
    have hp : lowerPayment 2401 = (268588726018:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2401+point 2 split 4096 2402)/2 = (477426593:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477426593:ℝ)/168755200)/ClassicalSixthBranch.v ((477426593:ℝ)/168755200) = (628346388593:ℝ)/305287516616 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2401
  · change lowerPayment 2402 ≤ lowerValue ((point 2 split 4096 2402+point 2 split 4096 2403)/2)
    have hp : lowerPayment 2402 = (268676999944:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2402+point 2 split 4096 2403)/2 = (95496971:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95496971:ℝ)/33751040)/ClassicalSixthBranch.v ((95496971:ℝ)/33751040) = (628269074919:ℝ)/305239508728 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2402
  · change lowerPayment 2403 ≤ lowerValue ((point 2 split 4096 2403+point 2 split 4096 2404)/2)
    have hp : lowerPayment 2403 = (268765269981:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2403+point 2 split 4096 2404)/2 = (477543117:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477543117:ℝ)/168755200)/ClassicalSixthBranch.v ((477543117:ℝ)/168755200) = (125638352249:ℝ)/61038300168 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2403
  · change lowerPayment 2404 ≤ lowerValue ((point 2 split 4096 2404+point 2 split 4096 2405)/2)
    have hp : lowerPayment 2404 = (268853536145:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2404+point 2 split 4096 2405)/2 = (477601379:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477601379:ℝ)/168755200)/ClassicalSixthBranch.v ((477601379:ℝ)/168755200) = (628114447571:ℝ)/305143492952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2404
  · change lowerPayment 2405 ≤ lowerValue ((point 2 split 4096 2405+point 2 split 4096 2406)/2)
    have hp : lowerPayment 2405 = (268941798449:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2405+point 2 split 4096 2406)/2 = (477659641:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477659641:ℝ)/168755200)/ClassicalSixthBranch.v ((477659641:ℝ)/168755200) = (628037133897:ℝ)/305095485064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2405
  · change lowerPayment 2406 ≤ lowerValue ((point 2 split 4096 2406+point 2 split 4096 2407)/2)
    have hp : lowerPayment 2406 = (269030056908:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2406+point 2 split 4096 2407)/2 = (477717903:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477717903:ℝ)/168755200)/ClassicalSixthBranch.v ((477717903:ℝ)/168755200) = (627959820223:ℝ)/305047477176 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2406
  · change lowerPayment 2407 ≤ lowerValue ((point 2 split 4096 2407+point 2 split 4096 2408)/2)
    have hp : lowerPayment 2407 = (269118311538:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2407+point 2 split 4096 2408)/2 = (95555233:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95555233:ℝ)/33751040)/ClassicalSixthBranch.v ((95555233:ℝ)/33751040) = (627882506549:ℝ)/304999469288 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2407
  · change lowerPayment 2408 ≤ lowerValue ((point 2 split 4096 2408+point 2 split 4096 2409)/2)
    have hp : lowerPayment 2408 = (269206562354:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2408+point 2 split 4096 2409)/2 = (477834427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477834427:ℝ)/168755200)/ClassicalSixthBranch.v ((477834427:ℝ)/168755200) = (25112207715:ℝ)/12198058456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2408
  · change lowerPayment 2409 ≤ lowerValue ((point 2 split 4096 2409+point 2 split 4096 2410)/2)
    have hp : lowerPayment 2409 = (269294809369:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2409+point 2 split 4096 2410)/2 = (477892689:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477892689:ℝ)/168755200)/ClassicalSixthBranch.v ((477892689:ℝ)/168755200) = (627727879201:ℝ)/304903453512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2409
  · change lowerPayment 2410 ≤ lowerValue ((point 2 split 4096 2410+point 2 split 4096 2411)/2)
    have hp : lowerPayment 2410 = (269383052599:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2410+point 2 split 4096 2411)/2 = (477950951:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((477950951:ℝ)/168755200)/ClassicalSixthBranch.v ((477950951:ℝ)/168755200) = (627650565527:ℝ)/304855445624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2410
  · change lowerPayment 2411 ≤ lowerValue ((point 2 split 4096 2411+point 2 split 4096 2412)/2)
    have hp : lowerPayment 2411 = (269471292058:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2411+point 2 split 4096 2412)/2 = (478009213:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478009213:ℝ)/168755200)/ClassicalSixthBranch.v ((478009213:ℝ)/168755200) = (627573251853:ℝ)/304807437736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2411
  · change lowerPayment 2412 ≤ lowerValue ((point 2 split 4096 2412+point 2 split 4096 2413)/2)
    have hp : lowerPayment 2412 = (269559527762:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2412+point 2 split 4096 2413)/2 = (19122699:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19122699:ℝ)/6750208)/ClassicalSixthBranch.v ((19122699:ℝ)/6750208) = (627495938179:ℝ)/304759429848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2412
  · change lowerPayment 2413 ≤ lowerValue ((point 2 split 4096 2413+point 2 split 4096 2414)/2)
    have hp : lowerPayment 2413 = (269647759725:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2413+point 2 split 4096 2414)/2 = (478125737:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478125737:ℝ)/168755200)/ClassicalSixthBranch.v ((478125737:ℝ)/168755200) = (125483724901:ℝ)/60942284392 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2413
  · change lowerPayment 2414 ≤ lowerValue ((point 2 split 4096 2414+point 2 split 4096 2415)/2)
    have hp : lowerPayment 2414 = (269735987962:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2414+point 2 split 4096 2415)/2 = (478183999:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478183999:ℝ)/168755200)/ClassicalSixthBranch.v ((478183999:ℝ)/168755200) = (627341310831:ℝ)/304663414072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2414
  · change lowerPayment 2415 ≤ lowerValue ((point 2 split 4096 2415+point 2 split 4096 2416)/2)
    have hp : lowerPayment 2415 = (269824212487:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2415+point 2 split 4096 2416)/2 = (478242261:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((478242261:ℝ)/168755200)/ClassicalSixthBranch.v ((478242261:ℝ)/168755200) = (627263997157:ℝ)/304615406184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2415
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_150
