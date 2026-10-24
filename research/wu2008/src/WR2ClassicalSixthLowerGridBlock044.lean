import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints044
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_044 (j : Fin 16) : lowerPayment (16*44+j.val) ≤
    lowerValue ((point 2 split 4096 (16*44+j.val)+point 2 split 4096 (16*44+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 704 ≤ lowerValue ((point 2 split 4096 704+point 2 split 4096 705)/2)
    have hp : lowerPayment 704 = (98960419218:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 704+point 2 split 4096 705)/2 = (378555979:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378555979:ℝ)/168755200)/ClassicalSixthBranch.v ((378555979:ℝ)/168755200) = (759547693371:ℝ)/386756902552 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_704
  · change lowerPayment 705 ≤ lowerValue ((point 2 split 4096 705+point 2 split 4096 706)/2)
    have hp : lowerPayment 705 = (99082452837:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 705+point 2 split 4096 706)/2 = (378614241:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378614241:ℝ)/168755200)/ClassicalSixthBranch.v ((378614241:ℝ)/168755200) = (759470379697:ℝ)/386708894664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_705
  · change lowerPayment 706 ≤ lowerValue ((point 2 split 4096 706+point 2 split 4096 707)/2)
    have hp : lowerPayment 706 = (99204444551:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 706+point 2 split 4096 707)/2 = (378672503:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378672503:ℝ)/168755200)/ClassicalSixthBranch.v ((378672503:ℝ)/168755200) = (759393066023:ℝ)/386660886776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_706
  · change lowerPayment 707 ≤ lowerValue ((point 2 split 4096 707+point 2 split 4096 708)/2)
    have hp : lowerPayment 707 = (99326394396:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 707+point 2 split 4096 708)/2 = (75746153:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75746153:ℝ)/33751040)/ClassicalSixthBranch.v ((75746153:ℝ)/33751040) = (759315752349:ℝ)/386612878888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_707
  · change lowerPayment 708 ≤ lowerValue ((point 2 split 4096 708+point 2 split 4096 709)/2)
    have hp : lowerPayment 708 = (99448302409:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 708+point 2 split 4096 709)/2 = (378789027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378789027:ℝ)/168755200)/ClassicalSixthBranch.v ((378789027:ℝ)/168755200) = (30369537547:ℝ)/15462594840 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_708
  · change lowerPayment 709 ≤ lowerValue ((point 2 split 4096 709+point 2 split 4096 710)/2)
    have hp : lowerPayment 709 = (99570168630:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 709+point 2 split 4096 710)/2 = (378847289:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378847289:ℝ)/168755200)/ClassicalSixthBranch.v ((378847289:ℝ)/168755200) = (759161125001:ℝ)/386516863112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_709
  · change lowerPayment 710 ≤ lowerValue ((point 2 split 4096 710+point 2 split 4096 711)/2)
    have hp : lowerPayment 710 = (99691993093:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 710+point 2 split 4096 711)/2 = (378905551:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378905551:ℝ)/168755200)/ClassicalSixthBranch.v ((378905551:ℝ)/168755200) = (759083811327:ℝ)/386468855224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_710
  · change lowerPayment 711 ≤ lowerValue ((point 2 split 4096 711+point 2 split 4096 712)/2)
    have hp : lowerPayment 711 = (99813775838:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 711+point 2 split 4096 712)/2 = (378963813:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((378963813:ℝ)/168755200)/ClassicalSixthBranch.v ((378963813:ℝ)/168755200) = (759006497653:ℝ)/386420847336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_711
  · change lowerPayment 712 ≤ lowerValue ((point 2 split 4096 712+point 2 split 4096 713)/2)
    have hp : lowerPayment 712 = (99935516900:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 712+point 2 split 4096 713)/2 = (15160883:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15160883:ℝ)/6750208)/ClassicalSixthBranch.v ((15160883:ℝ)/6750208) = (758929183979:ℝ)/386372839448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_712
  · change lowerPayment 713 ≤ lowerValue ((point 2 split 4096 713+point 2 split 4096 714)/2)
    have hp : lowerPayment 713 = (100057216318:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 713+point 2 split 4096 714)/2 = (379080337:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379080337:ℝ)/168755200)/ClassicalSixthBranch.v ((379080337:ℝ)/168755200) = (151770374061:ℝ)/77264966312 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_713
  · change lowerPayment 714 ≤ lowerValue ((point 2 split 4096 714+point 2 split 4096 715)/2)
    have hp : lowerPayment 714 = (100178874127:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 714+point 2 split 4096 715)/2 = (379138599:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379138599:ℝ)/168755200)/ClassicalSixthBranch.v ((379138599:ℝ)/168755200) = (758774556631:ℝ)/386276823672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_714
  · change lowerPayment 715 ≤ lowerValue ((point 2 split 4096 715+point 2 split 4096 716)/2)
    have hp : lowerPayment 715 = (100300490367:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 715+point 2 split 4096 716)/2 = (379196861:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379196861:ℝ)/168755200)/ClassicalSixthBranch.v ((379196861:ℝ)/168755200) = (758697242957:ℝ)/386228815784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_715
  · change lowerPayment 716 ≤ lowerValue ((point 2 split 4096 716+point 2 split 4096 717)/2)
    have hp : lowerPayment 716 = (100422065072:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 716+point 2 split 4096 717)/2 = (379255123:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379255123:ℝ)/168755200)/ClassicalSixthBranch.v ((379255123:ℝ)/168755200) = (758619929283:ℝ)/386180807896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_716
  · change lowerPayment 717 ≤ lowerValue ((point 2 split 4096 717+point 2 split 4096 718)/2)
    have hp : lowerPayment 717 = (100543598281:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 717+point 2 split 4096 718)/2 = (75862677:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((75862677:ℝ)/33751040)/ClassicalSixthBranch.v ((75862677:ℝ)/33751040) = (758542615609:ℝ)/386132800008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_717
  · change lowerPayment 718 ≤ lowerValue ((point 2 split 4096 718+point 2 split 4096 719)/2)
    have hp : lowerPayment 718 = (100665090031:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 718+point 2 split 4096 719)/2 = (379371647:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379371647:ℝ)/168755200)/ClassicalSixthBranch.v ((379371647:ℝ)/168755200) = (151693060387:ℝ)/77216958424 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_718
  · change lowerPayment 719 ≤ lowerValue ((point 2 split 4096 719+point 2 split 4096 720)/2)
    have hp : lowerPayment 719 = (100786540358:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 719+point 2 split 4096 720)/2 = (379429909:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((379429909:ℝ)/168755200)/ClassicalSixthBranch.v ((379429909:ℝ)/168755200) = (758387988261:ℝ)/386036784232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_719
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_044
