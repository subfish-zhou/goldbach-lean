import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints241
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_241 (j : Fin 16) : upperPayment (16*241+j.val) ≤
    upperValue ((point split endpoint 4096 (16*241+j.val)+point split endpoint 4096 (16*241+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3856 ≤ upperValue ((point split endpoint 4096 3856+point split endpoint 4096 3857)/2)
    have hp : upperPayment 3856 = (39225791401:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3856+point split endpoint 4096 3857)/2 = (673142527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673142527:ℝ)/168755200)*ClassicalSixthBranch.v ((673142527:ℝ)/168755200)/ClassicalSixthBranch.r = (77683652710545:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3856
  · change upperPayment 3857 ≤ upperValue ((point split endpoint 4096 3857+point split endpoint 4096 3858)/2)
    have hp : upperPayment 3857 = (39066951491:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3857+point split endpoint 4096 3858)/2 = (673167677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673167677:ℝ)/168755200)*ClassicalSixthBranch.v ((673167677:ℝ)/168755200)/ClassicalSixthBranch.r = (77665442239385:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3857
  · change upperPayment 3858 ≤ upperValue ((point split endpoint 4096 3858+point split endpoint 4096 3859)/2)
    have hp : upperPayment 3858 = (38908071035:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3858+point split endpoint 4096 3859)/2 = (673192827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673192827:ℝ)/168755200)*ClassicalSixthBranch.v ((673192827:ℝ)/168755200)/ClassicalSixthBranch.r = (77647233792297:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3858
  · change upperPayment 3859 ≤ upperValue ((point split endpoint 4096 3859+point split endpoint 4096 3860)/2)
    have hp : upperPayment 3859 = (38749150022:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3859+point split endpoint 4096 3860)/2 = (673217977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673217977:ℝ)/168755200)*ClassicalSixthBranch.v ((673217977:ℝ)/168755200)/ClassicalSixthBranch.r = (77629027369281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3859
  · change upperPayment 3860 ≤ upperValue ((point split endpoint 4096 3860+point split endpoint 4096 3861)/2)
    have hp : upperPayment 3860 = (38590188441:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3860+point split endpoint 4096 3861)/2 = (673243127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673243127:ℝ)/168755200)*ClassicalSixthBranch.v ((673243127:ℝ)/168755200)/ClassicalSixthBranch.r = (77610822970337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3860
  · change upperPayment 3861 ≤ upperValue ((point split endpoint 4096 3861+point split endpoint 4096 3862)/2)
    have hp : upperPayment 3861 = (38431186281:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3861+point split endpoint 4096 3862)/2 = (673268277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673268277:ℝ)/168755200)*ClassicalSixthBranch.v ((673268277:ℝ)/168755200)/ClassicalSixthBranch.r = (77592620595465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3861
  · change upperPayment 3862 ≤ upperValue ((point split endpoint 4096 3862+point split endpoint 4096 3863)/2)
    have hp : upperPayment 3862 = (38272143531:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3862+point split endpoint 4096 3863)/2 = (673293427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673293427:ℝ)/168755200)*ClassicalSixthBranch.v ((673293427:ℝ)/168755200)/ClassicalSixthBranch.r = (77574420244665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3862
  · change upperPayment 3863 ≤ upperValue ((point split endpoint 4096 3863+point split endpoint 4096 3864)/2)
    have hp : upperPayment 3863 = (38113060181:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3863+point split endpoint 4096 3864)/2 = (673318577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673318577:ℝ)/168755200)*ClassicalSixthBranch.v ((673318577:ℝ)/168755200)/ClassicalSixthBranch.r = (77556221917937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3863
  · change upperPayment 3864 ≤ upperValue ((point split endpoint 4096 3864+point split endpoint 4096 3865)/2)
    have hp : upperPayment 3864 = (37953936218:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3864+point split endpoint 4096 3865)/2 = (673343727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673343727:ℝ)/168755200)*ClassicalSixthBranch.v ((673343727:ℝ)/168755200)/ClassicalSixthBranch.r = (77538025615281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3864
  · change upperPayment 3865 ≤ upperValue ((point split endpoint 4096 3865+point split endpoint 4096 3866)/2)
    have hp : upperPayment 3865 = (37794771632:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3865+point split endpoint 4096 3866)/2 = (673368877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673368877:ℝ)/168755200)*ClassicalSixthBranch.v ((673368877:ℝ)/168755200)/ClassicalSixthBranch.r = (77519831336697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3865
  · change upperPayment 3866 ≤ upperValue ((point split endpoint 4096 3866+point split endpoint 4096 3867)/2)
    have hp : upperPayment 3866 = (37635566412:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3866+point split endpoint 4096 3867)/2 = (673394027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673394027:ℝ)/168755200)*ClassicalSixthBranch.v ((673394027:ℝ)/168755200)/ClassicalSixthBranch.r = (77501639082185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3866
  · change upperPayment 3867 ≤ upperValue ((point split endpoint 4096 3867+point split endpoint 4096 3868)/2)
    have hp : upperPayment 3867 = (37476320547:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3867+point split endpoint 4096 3868)/2 = (673419177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673419177:ℝ)/168755200)*ClassicalSixthBranch.v ((673419177:ℝ)/168755200)/ClassicalSixthBranch.r = (77483448851745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3867
  · change upperPayment 3868 ≤ upperValue ((point split endpoint 4096 3868+point split endpoint 4096 3869)/2)
    have hp : upperPayment 3868 = (37317034025:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3868+point split endpoint 4096 3869)/2 = (673444327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673444327:ℝ)/168755200)*ClassicalSixthBranch.v ((673444327:ℝ)/168755200)/ClassicalSixthBranch.r = (77465260645377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3868
  · change upperPayment 3869 ≤ upperValue ((point split endpoint 4096 3869+point split endpoint 4096 3870)/2)
    have hp : upperPayment 3869 = (37157706835:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3869+point split endpoint 4096 3870)/2 = (673469477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673469477:ℝ)/168755200)*ClassicalSixthBranch.v ((673469477:ℝ)/168755200)/ClassicalSixthBranch.r = (77447074463081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3869
  · change upperPayment 3870 ≤ upperValue ((point split endpoint 4096 3870+point split endpoint 4096 3871)/2)
    have hp : upperPayment 3870 = (36998338967:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3870+point split endpoint 4096 3871)/2 = (673494627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673494627:ℝ)/168755200)*ClassicalSixthBranch.v ((673494627:ℝ)/168755200)/ClassicalSixthBranch.r = (77428890304857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3870
  · change upperPayment 3871 ≤ upperValue ((point split endpoint 4096 3871+point split endpoint 4096 3872)/2)
    have hp : upperPayment 3871 = (36838930410:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3871+point split endpoint 4096 3872)/2 = (673519777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673519777:ℝ)/168755200)*ClassicalSixthBranch.v ((673519777:ℝ)/168755200)/ClassicalSixthBranch.r = (77410708170705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3871
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_241
