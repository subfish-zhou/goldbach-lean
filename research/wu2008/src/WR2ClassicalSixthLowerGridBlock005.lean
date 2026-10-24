import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints005
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_005 (j : Fin 16) : lowerPayment (16*5+j.val) ≤
    lowerValue ((point 2 split 4096 (16*5+j.val)+point 2 split 4096 (16*5+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 80 ≤ lowerValue ((point 2 split 4096 80+point 2 split 4096 81)/2)
    have hp : lowerPayment 80 = (12886430076:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 80+point 2 split 4096 81)/2 = (342200491:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342200491:ℝ)/168755200)/ClassicalSixthBranch.v ((342200491:ℝ)/168755200) = (807791425947:ℝ)/416713824664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_80
  · change lowerPayment 81 ≤ lowerValue ((point 2 split 4096 81+point 2 split 4096 82)/2)
    have hp : lowerPayment 81 = (13043450314:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 81+point 2 split 4096 82)/2 = (342258753:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342258753:ℝ)/168755200)/ClassicalSixthBranch.v ((342258753:ℝ)/168755200) = (807714112273:ℝ)/416665816776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_81
  · change lowerPayment 82 ≤ lowerValue ((point 2 split 4096 82+point 2 split 4096 83)/2)
    have hp : lowerPayment 82 = (13200397346:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 82+point 2 split 4096 83)/2 = (68463403:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68463403:ℝ)/33751040)/ClassicalSixthBranch.v ((68463403:ℝ)/33751040) = (807636798599:ℝ)/416617808888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_82
  · change lowerPayment 83 ≤ lowerValue ((point 2 split 4096 83+point 2 split 4096 84)/2)
    have hp : lowerPayment 83 = (13357271238:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 83+point 2 split 4096 84)/2 = (342375277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342375277:ℝ)/168755200)/ClassicalSixthBranch.v ((342375277:ℝ)/168755200) = (32302379397:ℝ)/16662792040 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_83
  · change lowerPayment 84 ≤ lowerValue ((point 2 split 4096 84+point 2 split 4096 85)/2)
    have hp : lowerPayment 84 = (13514072059:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 84+point 2 split 4096 85)/2 = (342433539:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342433539:ℝ)/168755200)/ClassicalSixthBranch.v ((342433539:ℝ)/168755200) = (807482171251:ℝ)/416521793112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_84
  · change lowerPayment 85 ≤ lowerValue ((point 2 split 4096 85+point 2 split 4096 86)/2)
    have hp : lowerPayment 85 = (13670799873:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 85+point 2 split 4096 86)/2 = (342491801:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342491801:ℝ)/168755200)/ClassicalSixthBranch.v ((342491801:ℝ)/168755200) = (807404857577:ℝ)/416473785224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_85
  · change lowerPayment 86 ≤ lowerValue ((point 2 split 4096 86+point 2 split 4096 87)/2)
    have hp : lowerPayment 86 = (13827454748:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 86+point 2 split 4096 87)/2 = (342550063:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342550063:ℝ)/168755200)/ClassicalSixthBranch.v ((342550063:ℝ)/168755200) = (807327543903:ℝ)/416425777336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_86
  · change lowerPayment 87 ≤ lowerValue ((point 2 split 4096 87+point 2 split 4096 88)/2)
    have hp : lowerPayment 87 = (13984036750:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 87+point 2 split 4096 88)/2 = (13704333:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((13704333:ℝ)/6750208)/ClassicalSixthBranch.v ((13704333:ℝ)/6750208) = (807250230229:ℝ)/416377769448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_87
  · change lowerPayment 88 ≤ lowerValue ((point 2 split 4096 88+point 2 split 4096 89)/2)
    have hp : lowerPayment 88 = (14140545947:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 88+point 2 split 4096 89)/2 = (342666587:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342666587:ℝ)/168755200)/ClassicalSixthBranch.v ((342666587:ℝ)/168755200) = (161434583311:ℝ)/83265952312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_88
  · change lowerPayment 89 ≤ lowerValue ((point 2 split 4096 89+point 2 split 4096 90)/2)
    have hp : lowerPayment 89 = (14296982403:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 89+point 2 split 4096 90)/2 = (342724849:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342724849:ℝ)/168755200)/ClassicalSixthBranch.v ((342724849:ℝ)/168755200) = (807095602881:ℝ)/416281753672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_89
  · change lowerPayment 90 ≤ lowerValue ((point 2 split 4096 90+point 2 split 4096 91)/2)
    have hp : lowerPayment 90 = (14453346186:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 90+point 2 split 4096 91)/2 = (342783111:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342783111:ℝ)/168755200)/ClassicalSixthBranch.v ((342783111:ℝ)/168755200) = (807018289207:ℝ)/416233745784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_90
  · change lowerPayment 91 ≤ lowerValue ((point 2 split 4096 91+point 2 split 4096 92)/2)
    have hp : lowerPayment 91 = (14609637361:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 91+point 2 split 4096 92)/2 = (342841373:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342841373:ℝ)/168755200)/ClassicalSixthBranch.v ((342841373:ℝ)/168755200) = (806940975533:ℝ)/416185737896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_91
  · change lowerPayment 92 ≤ lowerValue ((point 2 split 4096 92+point 2 split 4096 93)/2)
    have hp : lowerPayment 92 = (14765855995:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 92+point 2 split 4096 93)/2 = (68579927:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68579927:ℝ)/33751040)/ClassicalSixthBranch.v ((68579927:ℝ)/33751040) = (806863661859:ℝ)/416137730008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_92
  · change lowerPayment 93 ≤ lowerValue ((point 2 split 4096 93+point 2 split 4096 94)/2)
    have hp : lowerPayment 93 = (14922002155:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 93+point 2 split 4096 94)/2 = (342957897:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((342957897:ℝ)/168755200)/ClassicalSixthBranch.v ((342957897:ℝ)/168755200) = (161357269637:ℝ)/83217944424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_93
  · change lowerPayment 94 ≤ lowerValue ((point 2 split 4096 94+point 2 split 4096 95)/2)
    have hp : lowerPayment 94 = (15078075905:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 94+point 2 split 4096 95)/2 = (343016159:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343016159:ℝ)/168755200)/ClassicalSixthBranch.v ((343016159:ℝ)/168755200) = (806709034511:ℝ)/416041714232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_94
  · change lowerPayment 95 ≤ lowerValue ((point 2 split 4096 95+point 2 split 4096 96)/2)
    have hp : lowerPayment 95 = (15234077312:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 95+point 2 split 4096 96)/2 = (343074421:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((343074421:ℝ)/168755200)/ClassicalSixthBranch.v ((343074421:ℝ)/168755200) = (806631720837:ℝ)/415993706344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_95
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_005
