import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints154
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_154 (j : Fin 16) : lowerPayment (16*154+j.val) ≤
    lowerValue ((point 2 split 4096 (16*154+j.val)+point 2 split 4096 (16*154+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2464 ≤ lowerValue ((point 2 split 4096 2464+point 2 split 4096 2465)/2)
    have hp : lowerPayment 2464 = (274142974718:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2464+point 2 split 4096 2465)/2 = (481097099:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481097099:ℝ)/168755200)/ClassicalSixthBranch.v ((481097099:ℝ)/168755200) = (623475627131:ℝ)/302263019672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2464
  · change lowerPayment 2465 ≤ lowerValue ((point 2 split 4096 2465+point 2 split 4096 2466)/2)
    have hp : lowerPayment 2465 = (274231032448:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2465+point 2 split 4096 2466)/2 = (481155361:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481155361:ℝ)/168755200)/ClassicalSixthBranch.v ((481155361:ℝ)/168755200) = (623398313457:ℝ)/302215011784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2465
  · change lowerPayment 2466 ≤ lowerValue ((point 2 split 4096 2466+point 2 split 4096 2467)/2)
    have hp : lowerPayment 2466 = (274319087217:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2466+point 2 split 4096 2467)/2 = (481213623:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481213623:ℝ)/168755200)/ClassicalSixthBranch.v ((481213623:ℝ)/168755200) = (623320999783:ℝ)/302167003896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2466
  · change lowerPayment 2467 ≤ lowerValue ((point 2 split 4096 2467+point 2 split 4096 2468)/2)
    have hp : lowerPayment 2467 = (274407139038:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2467+point 2 split 4096 2468)/2 = (96254377:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96254377:ℝ)/33751040)/ClassicalSixthBranch.v ((96254377:ℝ)/33751040) = (623243686109:ℝ)/302118996008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2467
  · change lowerPayment 2468 ≤ lowerValue ((point 2 split 4096 2468+point 2 split 4096 2469)/2)
    have hp : lowerPayment 2468 = (274495187927:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2468+point 2 split 4096 2469)/2 = (481330147:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481330147:ℝ)/168755200)/ClassicalSixthBranch.v ((481330147:ℝ)/168755200) = (124633274487:ℝ)/60414197624 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2468
  · change lowerPayment 2469 ≤ lowerValue ((point 2 split 4096 2469+point 2 split 4096 2470)/2)
    have hp : lowerPayment 2469 = (274583233898:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2469+point 2 split 4096 2470)/2 = (481388409:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481388409:ℝ)/168755200)/ClassicalSixthBranch.v ((481388409:ℝ)/168755200) = (623089058761:ℝ)/302022980232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2469
  · change lowerPayment 2470 ≤ lowerValue ((point 2 split 4096 2470+point 2 split 4096 2471)/2)
    have hp : lowerPayment 2470 = (274671276966:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2470+point 2 split 4096 2471)/2 = (481446671:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481446671:ℝ)/168755200)/ClassicalSixthBranch.v ((481446671:ℝ)/168755200) = (623011745087:ℝ)/301974972344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2470
  · change lowerPayment 2471 ≤ lowerValue ((point 2 split 4096 2471+point 2 split 4096 2472)/2)
    have hp : lowerPayment 2471 = (274759317145:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2471+point 2 split 4096 2472)/2 = (481504933:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481504933:ℝ)/168755200)/ClassicalSixthBranch.v ((481504933:ℝ)/168755200) = (622934431413:ℝ)/301926964456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2471
  · change lowerPayment 2472 ≤ lowerValue ((point 2 split 4096 2472+point 2 split 4096 2473)/2)
    have hp : lowerPayment 2472 = (274847354450:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2472+point 2 split 4096 2473)/2 = (96312639:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96312639:ℝ)/33751040)/ClassicalSixthBranch.v ((96312639:ℝ)/33751040) = (622857117739:ℝ)/301878956568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2472
  · change lowerPayment 2473 ≤ lowerValue ((point 2 split 4096 2473+point 2 split 4096 2474)/2)
    have hp : lowerPayment 2473 = (274935388896:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2473+point 2 split 4096 2474)/2 = (481621457:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481621457:ℝ)/168755200)/ClassicalSixthBranch.v ((481621457:ℝ)/168755200) = (124555960813:ℝ)/60366189736 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2473
  · change lowerPayment 2474 ≤ lowerValue ((point 2 split 4096 2474+point 2 split 4096 2475)/2)
    have hp : lowerPayment 2474 = (275023420497:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2474+point 2 split 4096 2475)/2 = (481679719:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481679719:ℝ)/168755200)/ClassicalSixthBranch.v ((481679719:ℝ)/168755200) = (622702490391:ℝ)/301782940792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2474
  · change lowerPayment 2475 ≤ lowerValue ((point 2 split 4096 2475+point 2 split 4096 2476)/2)
    have hp : lowerPayment 2475 = (275111449268:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2475+point 2 split 4096 2476)/2 = (481737981:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481737981:ℝ)/168755200)/ClassicalSixthBranch.v ((481737981:ℝ)/168755200) = (622625176717:ℝ)/301734932904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2475
  · change lowerPayment 2476 ≤ lowerValue ((point 2 split 4096 2476+point 2 split 4096 2477)/2)
    have hp : lowerPayment 2476 = (275199475223:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2476+point 2 split 4096 2477)/2 = (481796243:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481796243:ℝ)/168755200)/ClassicalSixthBranch.v ((481796243:ℝ)/168755200) = (622547863043:ℝ)/301686925016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2476
  · change lowerPayment 2477 ≤ lowerValue ((point 2 split 4096 2477+point 2 split 4096 2478)/2)
    have hp : lowerPayment 2477 = (275287498377:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2477+point 2 split 4096 2478)/2 = (96370901:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((96370901:ℝ)/33751040)/ClassicalSixthBranch.v ((96370901:ℝ)/33751040) = (622470549369:ℝ)/301638917128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2477
  · change lowerPayment 2478 ≤ lowerValue ((point 2 split 4096 2478+point 2 split 4096 2479)/2)
    have hp : lowerPayment 2478 = (275375518744:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2478+point 2 split 4096 2479)/2 = (481912767:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481912767:ℝ)/168755200)/ClassicalSixthBranch.v ((481912767:ℝ)/168755200) = (124478647139:ℝ)/60318181848 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2478
  · change lowerPayment 2479 ≤ lowerValue ((point 2 split 4096 2479+point 2 split 4096 2480)/2)
    have hp : lowerPayment 2479 = (275463536340:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2479+point 2 split 4096 2480)/2 = (481971029:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((481971029:ℝ)/168755200)/ClassicalSixthBranch.v ((481971029:ℝ)/168755200) = (622315922021:ℝ)/301542901352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2479
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_154
