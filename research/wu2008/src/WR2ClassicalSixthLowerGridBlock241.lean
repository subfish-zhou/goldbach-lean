import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints241
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_241 (j : Fin 16) : lowerPayment (16*241+j.val) ≤
    lowerValue ((point 2 split 4096 (16*241+j.val)+point 2 split 4096 (16*241+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 3856 ≤ lowerValue ((point 2 split 4096 3856+point 2 split 4096 3857)/2)
    have hp : lowerPayment 3856 = (400291718340:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3856+point 2 split 4096 3857)/2 = (562197803:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562197803:ℝ)/168755200)/ClassicalSixthBranch.v ((562197803:ℝ)/168755200) = (515854992923:ℝ)/235436039576 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3856
  · change lowerPayment 3857 ≤ lowerValue ((point 2 split 4096 3857+point 2 split 4096 3858)/2)
    have hp : lowerPayment 3857 = (400389679365:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3857+point 2 split 4096 3858)/2 = (112451213:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112451213:ℝ)/33751040)/ClassicalSixthBranch.v ((112451213:ℝ)/33751040) = (515777679249:ℝ)/235388031688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3857
  · change lowerPayment 3858 ≤ lowerValue ((point 2 split 4096 3858+point 2 split 4096 3859)/2)
    have hp : lowerPayment 3858 = (400487658285:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3858+point 2 split 4096 3859)/2 = (562314327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562314327:ℝ)/168755200)/ClassicalSixthBranch.v ((562314327:ℝ)/168755200) = (20628014623:ℝ)/9413600952 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3858
  · change lowerPayment 3859 ≤ lowerValue ((point 2 split 4096 3859+point 2 split 4096 3860)/2)
    have hp : lowerPayment 3859 = (400585655116:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3859+point 2 split 4096 3860)/2 = (562372589:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562372589:ℝ)/168755200)/ClassicalSixthBranch.v ((562372589:ℝ)/168755200) = (515623051901:ℝ)/235292015912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3859
  · change lowerPayment 3860 ≤ lowerValue ((point 2 split 4096 3860+point 2 split 4096 3861)/2)
    have hp : lowerPayment 3860 = (400683669876:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3860+point 2 split 4096 3861)/2 = (562430851:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562430851:ℝ)/168755200)/ClassicalSixthBranch.v ((562430851:ℝ)/168755200) = (515545738227:ℝ)/235244008024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3860
  · change lowerPayment 3861 ≤ lowerValue ((point 2 split 4096 3861+point 2 split 4096 3862)/2)
    have hp : lowerPayment 3861 = (400781702584:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3861+point 2 split 4096 3862)/2 = (562489113:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562489113:ℝ)/168755200)/ClassicalSixthBranch.v ((562489113:ℝ)/168755200) = (515468424553:ℝ)/235196000136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3861
  · change lowerPayment 3862 ≤ lowerValue ((point 2 split 4096 3862+point 2 split 4096 3863)/2)
    have hp : lowerPayment 3862 = (400879753256:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3862+point 2 split 4096 3863)/2 = (218465:ℝ)/65536 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((218465:ℝ)/65536)/ClassicalSixthBranch.v ((218465:ℝ)/65536) = (5003797193:ℝ)/2282990216 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3862
  · change lowerPayment 3863 ≤ lowerValue ((point 2 split 4096 3863+point 2 split 4096 3864)/2)
    have hp : lowerPayment 3863 = (400977821911:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3863+point 2 split 4096 3864)/2 = (562605637:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562605637:ℝ)/168755200)/ClassicalSixthBranch.v ((562605637:ℝ)/168755200) = (103062759441:ℝ)/47019996872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3863
  · change lowerPayment 3864 ≤ lowerValue ((point 2 split 4096 3864+point 2 split 4096 3865)/2)
    have hp : lowerPayment 3864 = (401075908566:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3864+point 2 split 4096 3865)/2 = (562663899:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562663899:ℝ)/168755200)/ClassicalSixthBranch.v ((562663899:ℝ)/168755200) = (515236483531:ℝ)/235051976472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3864
  · change lowerPayment 3865 ≤ lowerValue ((point 2 split 4096 3865+point 2 split 4096 3866)/2)
    have hp : lowerPayment 3865 = (401174013239:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3865+point 2 split 4096 3866)/2 = (562722161:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562722161:ℝ)/168755200)/ClassicalSixthBranch.v ((562722161:ℝ)/168755200) = (515159169857:ℝ)/235003968584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3865
  · change lowerPayment 3866 ≤ lowerValue ((point 2 split 4096 3866+point 2 split 4096 3867)/2)
    have hp : lowerPayment 3866 = (401272135947:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3866+point 2 split 4096 3867)/2 = (562780423:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562780423:ℝ)/168755200)/ClassicalSixthBranch.v ((562780423:ℝ)/168755200) = (515081856183:ℝ)/234955960696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3866
  · change lowerPayment 3867 ≤ lowerValue ((point 2 split 4096 3867+point 2 split 4096 3868)/2)
    have hp : lowerPayment 3867 = (401370276709:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3867+point 2 split 4096 3868)/2 = (112567737:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((112567737:ℝ)/33751040)/ClassicalSixthBranch.v ((112567737:ℝ)/33751040) = (515004542509:ℝ)/234907952808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3867
  · change lowerPayment 3868 ≤ lowerValue ((point 2 split 4096 3868+point 2 split 4096 3869)/2)
    have hp : lowerPayment 3868 = (401468435542:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3868+point 2 split 4096 3869)/2 = (562896947:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562896947:ℝ)/168755200)/ClassicalSixthBranch.v ((562896947:ℝ)/168755200) = (102985445767:ℝ)/46971988984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3868
  · change lowerPayment 3869 ≤ lowerValue ((point 2 split 4096 3869+point 2 split 4096 3870)/2)
    have hp : lowerPayment 3869 = (401566612464:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3869+point 2 split 4096 3870)/2 = (562955209:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((562955209:ℝ)/168755200)/ClassicalSixthBranch.v ((562955209:ℝ)/168755200) = (514849915161:ℝ)/234811937032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3869
  · change lowerPayment 3870 ≤ lowerValue ((point 2 split 4096 3870+point 2 split 4096 3871)/2)
    have hp : lowerPayment 3870 = (401664807493:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3870+point 2 split 4096 3871)/2 = (563013471:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563013471:ℝ)/168755200)/ClassicalSixthBranch.v ((563013471:ℝ)/168755200) = (514772601487:ℝ)/234763929144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3870
  · change lowerPayment 3871 ≤ lowerValue ((point 2 split 4096 3871+point 2 split 4096 3872)/2)
    have hp : lowerPayment 3871 = (401763020646:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 3871+point 2 split 4096 3872)/2 = (563071733:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((563071733:ℝ)/168755200)/ClassicalSixthBranch.v ((563071733:ℝ)/168755200) = (514695287813:ℝ)/234715921256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_3871
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_241
