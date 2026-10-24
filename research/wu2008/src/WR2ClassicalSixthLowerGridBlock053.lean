import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints053
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_053 (j : Fin 16) : lowerPayment (16*53+j.val) ≤
    lowerValue ((point 2 split 4096 (16*53+j.val)+point 2 split 4096 (16*53+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 848 ≤ lowerValue ((point 2 split 4096 848+point 2 split 4096 849)/2)
    have hp : lowerPayment 848 = (116119489145:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 848+point 2 split 4096 849)/2 = (386945707:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((386945707:ℝ)/168755200)/ClassicalSixthBranch.v ((386945707:ℝ)/168755200) = (149682904863:ℝ)/75968753336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_848
  · change lowerPayment 849 ≤ lowerValue ((point 2 split 4096 849+point 2 split 4096 850)/2)
    have hp : lowerPayment 849 = (116235858457:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 849+point 2 split 4096 850)/2 = (387003969:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387003969:ℝ)/168755200)/ClassicalSixthBranch.v ((387003969:ℝ)/168755200) = (748337210641:ℝ)/379795758792 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_849
  · change lowerPayment 850 ≤ lowerValue ((point 2 split 4096 850+point 2 split 4096 851)/2)
    have hp : lowerPayment 850 = (116352190939:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 850+point 2 split 4096 851)/2 = (387062231:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387062231:ℝ)/168755200)/ClassicalSixthBranch.v ((387062231:ℝ)/168755200) = (748259896967:ℝ)/379747750904 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_850
  · change lowerPayment 851 ≤ lowerValue ((point 2 split 4096 851+point 2 split 4096 852)/2)
    have hp : lowerPayment 851 = (116468486627:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 851+point 2 split 4096 852)/2 = (387120493:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387120493:ℝ)/168755200)/ClassicalSixthBranch.v ((387120493:ℝ)/168755200) = (748182583293:ℝ)/379699743016 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_851
  · change lowerPayment 852 ≤ lowerValue ((point 2 split 4096 852+point 2 split 4096 853)/2)
    have hp : lowerPayment 852 = (116584745551:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 852+point 2 split 4096 853)/2 = (77435751:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77435751:ℝ)/33751040)/ClassicalSixthBranch.v ((77435751:ℝ)/33751040) = (748105269619:ℝ)/379651735128 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_852
  · change lowerPayment 853 ≤ lowerValue ((point 2 split 4096 853+point 2 split 4096 854)/2)
    have hp : lowerPayment 853 = (116700967747:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 853+point 2 split 4096 854)/2 = (387237017:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387237017:ℝ)/168755200)/ClassicalSixthBranch.v ((387237017:ℝ)/168755200) = (149605591189:ℝ)/75920745448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_853
  · change lowerPayment 854 ≤ lowerValue ((point 2 split 4096 854+point 2 split 4096 855)/2)
    have hp : lowerPayment 854 = (116817153247:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 854+point 2 split 4096 855)/2 = (387295279:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387295279:ℝ)/168755200)/ClassicalSixthBranch.v ((387295279:ℝ)/168755200) = (747950642271:ℝ)/379555719352 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_854
  · change lowerPayment 855 ≤ lowerValue ((point 2 split 4096 855+point 2 split 4096 856)/2)
    have hp : lowerPayment 855 = (116933302084:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 855+point 2 split 4096 856)/2 = (387353541:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387353541:ℝ)/168755200)/ClassicalSixthBranch.v ((387353541:ℝ)/168755200) = (747873328597:ℝ)/379507711464 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_855
  · change lowerPayment 856 ≤ lowerValue ((point 2 split 4096 856+point 2 split 4096 857)/2)
    have hp : lowerPayment 856 = (117049414292:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 856+point 2 split 4096 857)/2 = (387411803:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387411803:ℝ)/168755200)/ClassicalSixthBranch.v ((387411803:ℝ)/168755200) = (747796014923:ℝ)/379459703576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_856
  · change lowerPayment 857 ≤ lowerValue ((point 2 split 4096 857+point 2 split 4096 858)/2)
    have hp : lowerPayment 857 = (117165489902:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 857+point 2 split 4096 858)/2 = (77494013:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((77494013:ℝ)/33751040)/ClassicalSixthBranch.v ((77494013:ℝ)/33751040) = (747718701249:ℝ)/379411695688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_857
  · change lowerPayment 858 ≤ lowerValue ((point 2 split 4096 858+point 2 split 4096 859)/2)
    have hp : lowerPayment 858 = (117281528950:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 858+point 2 split 4096 859)/2 = (387528327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387528327:ℝ)/168755200)/ClassicalSixthBranch.v ((387528327:ℝ)/168755200) = (29905655503:ℝ)/15174547512 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_858
  · change lowerPayment 859 ≤ lowerValue ((point 2 split 4096 859+point 2 split 4096 860)/2)
    have hp : lowerPayment 859 = (117397531466:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 859+point 2 split 4096 860)/2 = (387586589:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387586589:ℝ)/168755200)/ClassicalSixthBranch.v ((387586589:ℝ)/168755200) = (747564073901:ℝ)/379315679912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_859
  · change lowerPayment 860 ≤ lowerValue ((point 2 split 4096 860+point 2 split 4096 861)/2)
    have hp : lowerPayment 860 = (117513497486:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 860+point 2 split 4096 861)/2 = (387644851:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387644851:ℝ)/168755200)/ClassicalSixthBranch.v ((387644851:ℝ)/168755200) = (747486760227:ℝ)/379267672024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_860
  · change lowerPayment 861 ≤ lowerValue ((point 2 split 4096 861+point 2 split 4096 862)/2)
    have hp : lowerPayment 861 = (117629427040:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 861+point 2 split 4096 862)/2 = (387703113:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387703113:ℝ)/168755200)/ClassicalSixthBranch.v ((387703113:ℝ)/168755200) = (747409446553:ℝ)/379219664136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_861
  · change lowerPayment 862 ≤ lowerValue ((point 2 split 4096 862+point 2 split 4096 863)/2)
    have hp : lowerPayment 862 = (117745320163:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 862+point 2 split 4096 863)/2 = (15510455:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((15510455:ℝ)/6750208)/ClassicalSixthBranch.v ((15510455:ℝ)/6750208) = (747332132879:ℝ)/379171656248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_862
  · change lowerPayment 863 ≤ lowerValue ((point 2 split 4096 863+point 2 split 4096 864)/2)
    have hp : lowerPayment 863 = (117861176888:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 863+point 2 split 4096 864)/2 = (387819637:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((387819637:ℝ)/168755200)/ClassicalSixthBranch.v ((387819637:ℝ)/168755200) = (149450963841:ℝ)/75824729672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_863
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_053
