import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints152
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_152 (j : Fin 16) : lowerPayment (16*152+j.val) ≤
    lowerValue ((point 2 split 4096 (16*152+j.val)+point 2 split 4096 (16*152+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2432 ≤ lowerValue ((point 2 split 4096 2432+point 2 split 4096 2433)/2)
    have hp : lowerPayment 2432 = (271323475888:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2432+point 2 split 4096 2433)/2 = (95846543:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95846543:ℝ)/33751040)/ClassicalSixthBranch.v ((95846543:ℝ)/33751040) = (1244432733:ℝ)/603974696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2432
  · change lowerPayment 2433 ≤ lowerValue ((point 2 split 4096 2433+point 2 split 4096 2434)/2)
    have hp : lowerPayment 2433 = (271411636133:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2433+point 2 split 4096 2434)/2 = (479290977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479290977:ℝ)/168755200)/ClassicalSixthBranch.v ((479290977:ℝ)/168755200) = (25034894041:ℝ)/12150050568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2433
  · change lowerPayment 2434 ≤ lowerValue ((point 2 split 4096 2434+point 2 split 4096 2435)/2)
    have hp : lowerPayment 2434 = (271499792946:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2434+point 2 split 4096 2435)/2 = (479349239:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479349239:ℝ)/168755200)/ClassicalSixthBranch.v ((479349239:ℝ)/168755200) = (625795037351:ℝ)/303703256312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2434
  · change lowerPayment 2435 ≤ lowerValue ((point 2 split 4096 2435+point 2 split 4096 2436)/2)
    have hp : lowerPayment 2435 = (271587946343:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2435+point 2 split 4096 2436)/2 = (479407501:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479407501:ℝ)/168755200)/ClassicalSixthBranch.v ((479407501:ℝ)/168755200) = (625717723677:ℝ)/303655248424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2435
  · change lowerPayment 2436 ≤ lowerValue ((point 2 split 4096 2436+point 2 split 4096 2437)/2)
    have hp : lowerPayment 2436 = (271676096338:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2436+point 2 split 4096 2437)/2 = (479465763:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479465763:ℝ)/168755200)/ClassicalSixthBranch.v ((479465763:ℝ)/168755200) = (625640410003:ℝ)/303607240536 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2436
  · change lowerPayment 2437 ≤ lowerValue ((point 2 split 4096 2437+point 2 split 4096 2438)/2)
    have hp : lowerPayment 2437 = (271764242946:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2437+point 2 split 4096 2438)/2 = (19180961:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((19180961:ℝ)/6750208)/ClassicalSixthBranch.v ((19180961:ℝ)/6750208) = (625563096329:ℝ)/303559232648 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2437
  · change lowerPayment 2438 ≤ lowerValue ((point 2 split 4096 2438+point 2 split 4096 2439)/2)
    have hp : lowerPayment 2438 = (271852386181:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2438+point 2 split 4096 2439)/2 = (479582287:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479582287:ℝ)/168755200)/ClassicalSixthBranch.v ((479582287:ℝ)/168755200) = (125097156531:ℝ)/60702244952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2438
  · change lowerPayment 2439 ≤ lowerValue ((point 2 split 4096 2439+point 2 split 4096 2440)/2)
    have hp : lowerPayment 2439 = (271940526059:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2439+point 2 split 4096 2440)/2 = (479640549:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479640549:ℝ)/168755200)/ClassicalSixthBranch.v ((479640549:ℝ)/168755200) = (625408468981:ℝ)/303463216872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2439
  · change lowerPayment 2440 ≤ lowerValue ((point 2 split 4096 2440+point 2 split 4096 2441)/2)
    have hp : lowerPayment 2440 = (272028662594:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2440+point 2 split 4096 2441)/2 = (479698811:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479698811:ℝ)/168755200)/ClassicalSixthBranch.v ((479698811:ℝ)/168755200) = (625331155307:ℝ)/303415208984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2440
  · change lowerPayment 2441 ≤ lowerValue ((point 2 split 4096 2441+point 2 split 4096 2442)/2)
    have hp : lowerPayment 2441 = (272116795801:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2441+point 2 split 4096 2442)/2 = (479757073:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479757073:ℝ)/168755200)/ClassicalSixthBranch.v ((479757073:ℝ)/168755200) = (625253841633:ℝ)/303367201096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2441
  · change lowerPayment 2442 ≤ lowerValue ((point 2 split 4096 2442+point 2 split 4096 2443)/2)
    have hp : lowerPayment 2442 = (272204925694:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2442+point 2 split 4096 2443)/2 = (95963067:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((95963067:ℝ)/33751040)/ClassicalSixthBranch.v ((95963067:ℝ)/33751040) = (625176527959:ℝ)/303319193208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2442
  · change lowerPayment 2443 ≤ lowerValue ((point 2 split 4096 2443+point 2 split 4096 2444)/2)
    have hp : lowerPayment 2443 = (272293052288:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2443+point 2 split 4096 2444)/2 = (479873597:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479873597:ℝ)/168755200)/ClassicalSixthBranch.v ((479873597:ℝ)/168755200) = (125019842857:ℝ)/60654237064 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2443
  · change lowerPayment 2444 ≤ lowerValue ((point 2 split 4096 2444+point 2 split 4096 2445)/2)
    have hp : lowerPayment 2444 = (272381175598:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2444+point 2 split 4096 2445)/2 = (479931859:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479931859:ℝ)/168755200)/ClassicalSixthBranch.v ((479931859:ℝ)/168755200) = (625021900611:ℝ)/303223177432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2444
  · change lowerPayment 2445 ≤ lowerValue ((point 2 split 4096 2445+point 2 split 4096 2446)/2)
    have hp : lowerPayment 2445 = (272469295639:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2445+point 2 split 4096 2446)/2 = (479990121:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((479990121:ℝ)/168755200)/ClassicalSixthBranch.v ((479990121:ℝ)/168755200) = (624944586937:ℝ)/303175169544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2445
  · change lowerPayment 2446 ≤ lowerValue ((point 2 split 4096 2446+point 2 split 4096 2447)/2)
    have hp : lowerPayment 2446 = (272557412425:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2446+point 2 split 4096 2447)/2 = (480048383:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((480048383:ℝ)/168755200)/ClassicalSixthBranch.v ((480048383:ℝ)/168755200) = (624867273263:ℝ)/303127161656 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2446
  · change lowerPayment 2447 ≤ lowerValue ((point 2 split 4096 2447+point 2 split 4096 2448)/2)
    have hp : lowerPayment 2447 = (272645525971:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2447+point 2 split 4096 2448)/2 = (96021329:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96021329:ℝ)/33751040)/ClassicalSixthBranch.v ((96021329:ℝ)/33751040) = (624789959589:ℝ)/303079153768 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2447
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_152
