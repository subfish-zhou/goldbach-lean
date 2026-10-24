import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints240
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_240 (j : Fin 16) : upperPayment (16*240+j.val) ≤
    upperValue ((point split endpoint 4096 (16*240+j.val)+point split endpoint 4096 (16*240+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3840 ≤ upperValue ((point split endpoint 4096 3840+point split endpoint 4096 3841)/2)
    have hp : upperPayment 3840 = (41761724752:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3840+point split endpoint 4096 3841)/2 = (672740127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672740127:ℝ)/168755200)*ClassicalSixthBranch.v ((672740127:ℝ)/168755200)/ClassicalSixthBranch.r = (77975295522897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3840
  · change upperPayment 3841 ≤ upperValue ((point split endpoint 4096 3841+point split endpoint 4096 3842)/2)
    have hp : upperPayment 3841 = (41603532074:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3841+point split endpoint 4096 3842)/2 = (672765277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672765277:ℝ)/168755200)*ClassicalSixthBranch.v ((672765277:ℝ)/168755200)/ClassicalSixthBranch.r = (77957052666585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3841
  · change upperPayment 3842 ≤ upperValue ((point split endpoint 4096 3842+point split endpoint 4096 3843)/2)
    have hp : upperPayment 3842 = (41445299026:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3842+point split endpoint 4096 3843)/2 = (672790427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672790427:ℝ)/168755200)*ClassicalSixthBranch.v ((672790427:ℝ)/168755200)/ClassicalSixthBranch.r = (77938811834345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3842
  · change upperPayment 3843 ≤ upperValue ((point split endpoint 4096 3843+point split endpoint 4096 3844)/2)
    have hp : upperPayment 3843 = (41287025598:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3843+point split endpoint 4096 3844)/2 = (672815577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672815577:ℝ)/168755200)*ClassicalSixthBranch.v ((672815577:ℝ)/168755200)/ClassicalSixthBranch.r = (77920573026177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3843
  · change upperPayment 3844 ≤ upperValue ((point split endpoint 4096 3844+point split endpoint 4096 3845)/2)
    have hp : upperPayment 3844 = (41128711778:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3844+point split endpoint 4096 3845)/2 = (672840727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672840727:ℝ)/168755200)*ClassicalSixthBranch.v ((672840727:ℝ)/168755200)/ClassicalSixthBranch.r = (77902336242081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3844
  · change upperPayment 3845 ≤ upperValue ((point split endpoint 4096 3845+point split endpoint 4096 3846)/2)
    have hp : upperPayment 3845 = (40970357556:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3845+point split endpoint 4096 3846)/2 = (672865877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672865877:ℝ)/168755200)*ClassicalSixthBranch.v ((672865877:ℝ)/168755200)/ClassicalSixthBranch.r = (77884101482057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3845
  · change upperPayment 3846 ≤ upperValue ((point split endpoint 4096 3846+point split endpoint 4096 3847)/2)
    have hp : upperPayment 3846 = (40811962920:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3846+point split endpoint 4096 3847)/2 = (672891027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672891027:ℝ)/168755200)*ClassicalSixthBranch.v ((672891027:ℝ)/168755200)/ClassicalSixthBranch.r = (77865868746105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3846
  · change upperPayment 3847 ≤ upperValue ((point split endpoint 4096 3847+point split endpoint 4096 3848)/2)
    have hp : upperPayment 3847 = (40653527860:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3847+point split endpoint 4096 3848)/2 = (672916177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672916177:ℝ)/168755200)*ClassicalSixthBranch.v ((672916177:ℝ)/168755200)/ClassicalSixthBranch.r = (77847638034225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3847
  · change upperPayment 3848 ≤ upperValue ((point split endpoint 4096 3848+point split endpoint 4096 3849)/2)
    have hp : upperPayment 3848 = (40495052365:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3848+point split endpoint 4096 3849)/2 = (672941327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672941327:ℝ)/168755200)*ClassicalSixthBranch.v ((672941327:ℝ)/168755200)/ClassicalSixthBranch.r = (77829409346417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3848
  · change upperPayment 3849 ≤ upperValue ((point split endpoint 4096 3849+point split endpoint 4096 3850)/2)
    have hp : upperPayment 3849 = (40336536422:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3849+point split endpoint 4096 3850)/2 = (672966477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672966477:ℝ)/168755200)*ClassicalSixthBranch.v ((672966477:ℝ)/168755200)/ClassicalSixthBranch.r = (77811182682681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3849
  · change upperPayment 3850 ≤ upperValue ((point split endpoint 4096 3850+point split endpoint 4096 3851)/2)
    have hp : upperPayment 3850 = (40177980023:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3850+point split endpoint 4096 3851)/2 = (672991627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((672991627:ℝ)/168755200)*ClassicalSixthBranch.v ((672991627:ℝ)/168755200)/ClassicalSixthBranch.r = (77792958043017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3850
  · change upperPayment 3851 ≤ upperValue ((point split endpoint 4096 3851+point split endpoint 4096 3852)/2)
    have hp : upperPayment 3851 = (40019383155:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3851+point split endpoint 4096 3852)/2 = (673016777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673016777:ℝ)/168755200)*ClassicalSixthBranch.v ((673016777:ℝ)/168755200)/ClassicalSixthBranch.r = (77774735427425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3851
  · change upperPayment 3852 ≤ upperValue ((point split endpoint 4096 3852+point split endpoint 4096 3853)/2)
    have hp : upperPayment 3852 = (39860745807:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3852+point split endpoint 4096 3853)/2 = (673041927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673041927:ℝ)/168755200)*ClassicalSixthBranch.v ((673041927:ℝ)/168755200)/ClassicalSixthBranch.r = (77756514835905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3852
  · change upperPayment 3853 ≤ upperValue ((point split endpoint 4096 3853+point split endpoint 4096 3854)/2)
    have hp : upperPayment 3853 = (39702067969:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3853+point split endpoint 4096 3854)/2 = (673067077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673067077:ℝ)/168755200)*ClassicalSixthBranch.v ((673067077:ℝ)/168755200)/ClassicalSixthBranch.r = (77738296268457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3853
  · change upperPayment 3854 ≤ upperValue ((point split endpoint 4096 3854+point split endpoint 4096 3855)/2)
    have hp : upperPayment 3854 = (39543349629:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3854+point split endpoint 4096 3855)/2 = (673092227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673092227:ℝ)/168755200)*ClassicalSixthBranch.v ((673092227:ℝ)/168755200)/ClassicalSixthBranch.r = (77720079725081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3854
  · change upperPayment 3855 ≤ upperValue ((point split endpoint 4096 3855+point split endpoint 4096 3856)/2)
    have hp : upperPayment 3855 = (39384590777:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3855+point split endpoint 4096 3856)/2 = (673117377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((673117377:ℝ)/168755200)*ClassicalSixthBranch.v ((673117377:ℝ)/168755200)/ClassicalSixthBranch.r = (77701865205777:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3855
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_240
