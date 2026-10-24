import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints181
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_181 (j : Fin 16) : upperPayment (16*181+j.val) ≤
    upperValue ((point split endpoint 4096 (16*181+j.val)+point split endpoint 4096 (16*181+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2896 ≤ upperValue ((point split endpoint 4096 2896+point split endpoint 4096 2897)/2)
    have hp : upperPayment 2896 = (174490408219:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2896+point split endpoint 4096 2897)/2 = (648998527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648998527:ℝ)/168755200)*ClassicalSixthBranch.v ((648998527:ℝ)/168755200)/ClassicalSixthBranch.r = (96099368956305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2896
  · change upperPayment 2897 ≤ upperValue ((point split endpoint 4096 2897+point split endpoint 4096 2898)/2)
    have hp : upperPayment 2897 = (174366017774:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2897+point split endpoint 4096 2898)/2 = (649023677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649023677:ℝ)/168755200)*ClassicalSixthBranch.v ((649023677:ℝ)/168755200)/ClassicalSixthBranch.r = (96079215376025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2897
  · change upperPayment 2898 ≤ upperValue ((point split endpoint 4096 2898+point split endpoint 4096 2899)/2)
    have hp : upperPayment 2898 = (174241595519:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2898+point split endpoint 4096 2899)/2 = (649048827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649048827:ℝ)/168755200)*ClassicalSixthBranch.v ((649048827:ℝ)/168755200)/ClassicalSixthBranch.r = (96059063819817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2898
  · change upperPayment 2899 ≤ upperValue ((point split endpoint 4096 2899+point split endpoint 4096 2900)/2)
    have hp : upperPayment 2899 = (174117141446:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2899+point split endpoint 4096 2900)/2 = (649073977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649073977:ℝ)/168755200)*ClassicalSixthBranch.v ((649073977:ℝ)/168755200)/ClassicalSixthBranch.r = (96038914287681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2899
  · change upperPayment 2900 ≤ upperValue ((point split endpoint 4096 2900+point split endpoint 4096 2901)/2)
    have hp : upperPayment 2900 = (173992655548:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2900+point split endpoint 4096 2901)/2 = (649099127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649099127:ℝ)/168755200)*ClassicalSixthBranch.v ((649099127:ℝ)/168755200)/ClassicalSixthBranch.r = (96018766779617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2900
  · change upperPayment 2901 ≤ upperValue ((point split endpoint 4096 2901+point split endpoint 4096 2902)/2)
    have hp : upperPayment 2901 = (173868137817:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2901+point split endpoint 4096 2902)/2 = (649124277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649124277:ℝ)/168755200)*ClassicalSixthBranch.v ((649124277:ℝ)/168755200)/ClassicalSixthBranch.r = (95998621295625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2901
  · change upperPayment 2902 ≤ upperValue ((point split endpoint 4096 2902+point split endpoint 4096 2903)/2)
    have hp : upperPayment 2902 = (173743588247:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2902+point split endpoint 4096 2903)/2 = (649149427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649149427:ℝ)/168755200)*ClassicalSixthBranch.v ((649149427:ℝ)/168755200)/ClassicalSixthBranch.r = (95978477835705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2902
  · change upperPayment 2903 ≤ upperValue ((point split endpoint 4096 2903+point split endpoint 4096 2904)/2)
    have hp : upperPayment 2903 = (173619006828:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2903+point split endpoint 4096 2904)/2 = (649174577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649174577:ℝ)/168755200)*ClassicalSixthBranch.v ((649174577:ℝ)/168755200)/ClassicalSixthBranch.r = (95958336399857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2903
  · change upperPayment 2904 ≤ upperValue ((point split endpoint 4096 2904+point split endpoint 4096 2905)/2)
    have hp : upperPayment 2904 = (173494393555:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2904+point split endpoint 4096 2905)/2 = (649199727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649199727:ℝ)/168755200)*ClassicalSixthBranch.v ((649199727:ℝ)/168755200)/ClassicalSixthBranch.r = (95938196988081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2904
  · change upperPayment 2905 ≤ upperValue ((point split endpoint 4096 2905+point split endpoint 4096 2906)/2)
    have hp : upperPayment 2905 = (173369748419:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2905+point split endpoint 4096 2906)/2 = (649224877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649224877:ℝ)/168755200)*ClassicalSixthBranch.v ((649224877:ℝ)/168755200)/ClassicalSixthBranch.r = (95918059600377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2905
  · change upperPayment 2906 ≤ upperValue ((point split endpoint 4096 2906+point split endpoint 4096 2907)/2)
    have hp : upperPayment 2906 = (173245071413:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2906+point split endpoint 4096 2907)/2 = (649250027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649250027:ℝ)/168755200)*ClassicalSixthBranch.v ((649250027:ℝ)/168755200)/ClassicalSixthBranch.r = (95897924236745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2906
  · change upperPayment 2907 ≤ upperValue ((point split endpoint 4096 2907+point split endpoint 4096 2908)/2)
    have hp : upperPayment 2907 = (173120362530:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2907+point split endpoint 4096 2908)/2 = (649275177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649275177:ℝ)/168755200)*ClassicalSixthBranch.v ((649275177:ℝ)/168755200)/ClassicalSixthBranch.r = (95877790897185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2907
  · change upperPayment 2908 ≤ upperValue ((point split endpoint 4096 2908+point split endpoint 4096 2909)/2)
    have hp : upperPayment 2908 = (172995621763:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2908+point split endpoint 4096 2909)/2 = (649300327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649300327:ℝ)/168755200)*ClassicalSixthBranch.v ((649300327:ℝ)/168755200)/ClassicalSixthBranch.r = (95857659581697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2908
  · change upperPayment 2909 ≤ upperValue ((point split endpoint 4096 2909+point split endpoint 4096 2910)/2)
    have hp : upperPayment 2909 = (172870849103:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2909+point split endpoint 4096 2910)/2 = (649325477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649325477:ℝ)/168755200)*ClassicalSixthBranch.v ((649325477:ℝ)/168755200)/ClassicalSixthBranch.r = (95837530290281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2909
  · change upperPayment 2910 ≤ upperValue ((point split endpoint 4096 2910+point split endpoint 4096 2911)/2)
    have hp : upperPayment 2910 = (172746044543:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2910+point split endpoint 4096 2911)/2 = (649350627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649350627:ℝ)/168755200)*ClassicalSixthBranch.v ((649350627:ℝ)/168755200)/ClassicalSixthBranch.r = (95817403022937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2910
  · change upperPayment 2911 ≤ upperValue ((point split endpoint 4096 2911+point split endpoint 4096 2912)/2)
    have hp : upperPayment 2911 = (172621208077:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2911+point split endpoint 4096 2912)/2 = (649375777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649375777:ℝ)/168755200)*ClassicalSixthBranch.v ((649375777:ℝ)/168755200)/ClassicalSixthBranch.r = (930070658055:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2911
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_181
