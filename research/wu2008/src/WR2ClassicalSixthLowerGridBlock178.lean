import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints178
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_178 (j : Fin 16) : lowerPayment (16*178+j.val) ≤
    lowerValue ((point 2 split 4096 (16*178+j.val)+point 2 split 4096 (16*178+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2848 ≤ lowerValue ((point 2 split 4096 2848+point 2 split 4096 2849)/2)
    have hp : lowerPayment 2848 = (307874376450:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2848+point 2 split 4096 2849)/2 = (503469707:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503469707:ℝ)/168755200)/ClassicalSixthBranch.v ((503469707:ℝ)/168755200) = (118757435263:ℝ)/56765598136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2848
  · change lowerPayment 2849 ≤ lowerValue ((point 2 split 4096 2849+point 2 split 4096 2850)/2)
    have hp : lowerPayment 2849 = (307962353485:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2849+point 2 split 4096 2850)/2 = (503527969:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503527969:ℝ)/168755200)/ClassicalSixthBranch.v ((503527969:ℝ)/168755200) = (593709862641:ℝ)/283779982792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2849
  · change lowerPayment 2850 ≤ lowerValue ((point 2 split 4096 2850+point 2 split 4096 2851)/2)
    have hp : lowerPayment 2850 = (308050333043:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2850+point 2 split 4096 2851)/2 = (503586231:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503586231:ℝ)/168755200)/ClassicalSixthBranch.v ((503586231:ℝ)/168755200) = (593632548967:ℝ)/283731974904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2850
  · change lowerPayment 2851 ≤ lowerValue ((point 2 split 4096 2851+point 2 split 4096 2852)/2)
    have hp : lowerPayment 2851 = (308138315137:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2851+point 2 split 4096 2852)/2 = (503644493:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503644493:ℝ)/168755200)/ClassicalSixthBranch.v ((503644493:ℝ)/168755200) = (593555235293:ℝ)/283683967016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2851
  · change lowerPayment 2852 ≤ lowerValue ((point 2 split 4096 2852+point 2 split 4096 2853)/2)
    have hp : lowerPayment 2852 = (308226299782:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2852+point 2 split 4096 2853)/2 = (100740551:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100740551:ℝ)/33751040)/ClassicalSixthBranch.v ((100740551:ℝ)/33751040) = (593477921619:ℝ)/283635959128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2852
  · change lowerPayment 2853 ≤ lowerValue ((point 2 split 4096 2853+point 2 split 4096 2854)/2)
    have hp : lowerPayment 2853 = (308314286991:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2853+point 2 split 4096 2854)/2 = (503761017:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503761017:ℝ)/168755200)/ClassicalSixthBranch.v ((503761017:ℝ)/168755200) = (118680121589:ℝ)/56717590248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2853
  · change lowerPayment 2854 ≤ lowerValue ((point 2 split 4096 2854+point 2 split 4096 2855)/2)
    have hp : lowerPayment 2854 = (308402276780:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2854+point 2 split 4096 2855)/2 = (503819279:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503819279:ℝ)/168755200)/ClassicalSixthBranch.v ((503819279:ℝ)/168755200) = (593323294271:ℝ)/283539943352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2854
  · change lowerPayment 2855 ≤ lowerValue ((point 2 split 4096 2855+point 2 split 4096 2856)/2)
    have hp : lowerPayment 2855 = (308490269161:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2855+point 2 split 4096 2856)/2 = (503877541:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503877541:ℝ)/168755200)/ClassicalSixthBranch.v ((503877541:ℝ)/168755200) = (593245980597:ℝ)/283491935464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2855
  · change lowerPayment 2856 ≤ lowerValue ((point 2 split 4096 2856+point 2 split 4096 2857)/2)
    have hp : lowerPayment 2856 = (308578264150:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2856+point 2 split 4096 2857)/2 = (503935803:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((503935803:ℝ)/168755200)/ClassicalSixthBranch.v ((503935803:ℝ)/168755200) = (593168666923:ℝ)/283443927576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2856
  · change lowerPayment 2857 ≤ lowerValue ((point 2 split 4096 2857+point 2 split 4096 2858)/2)
    have hp : lowerPayment 2857 = (308666261759:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2857+point 2 split 4096 2858)/2 = (100798813:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((100798813:ℝ)/33751040)/ClassicalSixthBranch.v ((100798813:ℝ)/33751040) = (593091353249:ℝ)/283395919688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2857
  · change lowerPayment 2858 ≤ lowerValue ((point 2 split 4096 2858+point 2 split 4096 2859)/2)
    have hp : lowerPayment 2858 = (308754262004:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2858+point 2 split 4096 2859)/2 = (504052327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504052327:ℝ)/168755200)/ClassicalSixthBranch.v ((504052327:ℝ)/168755200) = (23720561583:ℝ)/11333916472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2858
  · change lowerPayment 2859 ≤ lowerValue ((point 2 split 4096 2859+point 2 split 4096 2860)/2)
    have hp : lowerPayment 2859 = (308842264899:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2859+point 2 split 4096 2860)/2 = (504110589:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504110589:ℝ)/168755200)/ClassicalSixthBranch.v ((504110589:ℝ)/168755200) = (592936725901:ℝ)/283299903912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2859
  · change lowerPayment 2860 ≤ lowerValue ((point 2 split 4096 2860+point 2 split 4096 2861)/2)
    have hp : lowerPayment 2860 = (308930270457:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2860+point 2 split 4096 2861)/2 = (504168851:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504168851:ℝ)/168755200)/ClassicalSixthBranch.v ((504168851:ℝ)/168755200) = (592859412227:ℝ)/283251896024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2860
  · change lowerPayment 2861 ≤ lowerValue ((point 2 split 4096 2861+point 2 split 4096 2862)/2)
    have hp : lowerPayment 2861 = (309018278692:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2861+point 2 split 4096 2862)/2 = (504227113:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504227113:ℝ)/168755200)/ClassicalSixthBranch.v ((504227113:ℝ)/168755200) = (592782098553:ℝ)/283203888136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2861
  · change lowerPayment 2862 ≤ lowerValue ((point 2 split 4096 2862+point 2 split 4096 2863)/2)
    have hp : lowerPayment 2862 = (309106289619:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2862+point 2 split 4096 2863)/2 = (20171415:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((20171415:ℝ)/6750208)/ClassicalSixthBranch.v ((20171415:ℝ)/6750208) = (592704784879:ℝ)/283155880248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2862
  · change lowerPayment 2863 ≤ lowerValue ((point 2 split 4096 2863+point 2 split 4096 2864)/2)
    have hp : lowerPayment 2863 = (309194303252:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2863+point 2 split 4096 2864)/2 = (504343637:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((504343637:ℝ)/168755200)/ClassicalSixthBranch.v ((504343637:ℝ)/168755200) = (118525494241:ℝ)/56621574472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2863
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_178
