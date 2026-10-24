import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints245
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_245 (j : Fin 16) : upperPayment (16*245+j.val) ≤
    upperValue ((point split endpoint 4096 (16*245+j.val)+point split endpoint 4096 (16*245+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3920 ≤ upperValue ((point split endpoint 4096 3920+point split endpoint 4096 3921)/2)
    have hp : upperPayment 3920 = (28977833555:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3920+point split endpoint 4096 3921)/2 = (674752127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674752127:ℝ)/168755200)*ClassicalSixthBranch.v ((674752127:ℝ)/168755200)/ClassicalSixthBranch.r = (76522263085457:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3920
  · change upperPayment 3921 ≤ upperValue ((point split endpoint 4096 3921+point split endpoint 4096 3922)/2)
    have hp : upperPayment 3921 = (28816376243:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3921+point split endpoint 4096 3922)/2 = (674777277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674777277:ℝ)/168755200)*ClassicalSixthBranch.v ((674777277:ℝ)/168755200)/ClassicalSixthBranch.r = (76504182154905:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3921
  · change upperPayment 3922 ≤ upperValue ((point split endpoint 4096 3922+point split endpoint 4096 3923)/2)
    have hp : upperPayment 3922 = (28654877669:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3922+point split endpoint 4096 3923)/2 = (674802427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674802427:ℝ)/168755200)*ClassicalSixthBranch.v ((674802427:ℝ)/168755200)/ClassicalSixthBranch.r = (76486103248425:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3922
  · change upperPayment 3923 ≤ upperValue ((point split endpoint 4096 3923+point split endpoint 4096 3924)/2)
    have hp : upperPayment 3923 = (28493337820:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3923+point split endpoint 4096 3924)/2 = (674827577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674827577:ℝ)/168755200)*ClassicalSixthBranch.v ((674827577:ℝ)/168755200)/ClassicalSixthBranch.r = (76468026366017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3923
  · change upperPayment 3924 ≤ upperValue ((point split endpoint 4096 3924+point split endpoint 4096 3925)/2)
    have hp : upperPayment 3924 = (28331756687:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3924+point split endpoint 4096 3925)/2 = (674852727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674852727:ℝ)/168755200)*ClassicalSixthBranch.v ((674852727:ℝ)/168755200)/ClassicalSixthBranch.r = (76449951507681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3924
  · change upperPayment 3925 ≤ upperValue ((point split endpoint 4096 3925+point split endpoint 4096 3926)/2)
    have hp : upperPayment 3925 = (28170134257:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3925+point split endpoint 4096 3926)/2 = (674877877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674877877:ℝ)/168755200)*ClassicalSixthBranch.v ((674877877:ℝ)/168755200)/ClassicalSixthBranch.r = (76431878673417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3925
  · change upperPayment 3926 ≤ upperValue ((point split endpoint 4096 3926+point split endpoint 4096 3927)/2)
    have hp : upperPayment 3926 = (28008470518:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3926+point split endpoint 4096 3927)/2 = (674903027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674903027:ℝ)/168755200)*ClassicalSixthBranch.v ((674903027:ℝ)/168755200)/ClassicalSixthBranch.r = (76413807863225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3926
  · change upperPayment 3927 ≤ upperValue ((point split endpoint 4096 3927+point split endpoint 4096 3928)/2)
    have hp : upperPayment 3927 = (27846765461:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3927+point split endpoint 4096 3928)/2 = (674928177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674928177:ℝ)/168755200)*ClassicalSixthBranch.v ((674928177:ℝ)/168755200)/ClassicalSixthBranch.r = (76395739077105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3927
  · change upperPayment 3928 ≤ upperValue ((point split endpoint 4096 3928+point split endpoint 4096 3929)/2)
    have hp : upperPayment 3928 = (27685019072:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3928+point split endpoint 4096 3929)/2 = (674953327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674953327:ℝ)/168755200)*ClassicalSixthBranch.v ((674953327:ℝ)/168755200)/ClassicalSixthBranch.r = (76377672315057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3928
  · change upperPayment 3929 ≤ upperValue ((point split endpoint 4096 3929+point split endpoint 4096 3930)/2)
    have hp : upperPayment 3929 = (27523231342:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3929+point split endpoint 4096 3930)/2 = (674978477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((674978477:ℝ)/168755200)*ClassicalSixthBranch.v ((674978477:ℝ)/168755200)/ClassicalSixthBranch.r = (76359607577081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3929
  · change upperPayment 3930 ≤ upperValue ((point split endpoint 4096 3930+point split endpoint 4096 3931)/2)
    have hp : upperPayment 3930 = (27361402258:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3930+point split endpoint 4096 3931)/2 = (675003627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675003627:ℝ)/168755200)*ClassicalSixthBranch.v ((675003627:ℝ)/168755200)/ClassicalSixthBranch.r = (76341544863177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3930
  · change upperPayment 3931 ≤ upperValue ((point split endpoint 4096 3931+point split endpoint 4096 3932)/2)
    have hp : upperPayment 3931 = (27199531809:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3931+point split endpoint 4096 3932)/2 = (675028777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675028777:ℝ)/168755200)*ClassicalSixthBranch.v ((675028777:ℝ)/168755200)/ClassicalSixthBranch.r = (76323484173345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3931
  · change upperPayment 3932 ≤ upperValue ((point split endpoint 4096 3932+point split endpoint 4096 3933)/2)
    have hp : upperPayment 3932 = (27037619983:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3932+point split endpoint 4096 3933)/2 = (675053927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675053927:ℝ)/168755200)*ClassicalSixthBranch.v ((675053927:ℝ)/168755200)/ClassicalSixthBranch.r = (76305425507585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3932
  · change upperPayment 3933 ≤ upperValue ((point split endpoint 4096 3933+point split endpoint 4096 3934)/2)
    have hp : upperPayment 3933 = (26875666770:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3933+point split endpoint 4096 3934)/2 = (675079077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675079077:ℝ)/168755200)*ClassicalSixthBranch.v ((675079077:ℝ)/168755200)/ClassicalSixthBranch.r = (76287368865897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3933
  · change upperPayment 3934 ≤ upperValue ((point split endpoint 4096 3934+point split endpoint 4096 3935)/2)
    have hp : upperPayment 3934 = (26713672158:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3934+point split endpoint 4096 3935)/2 = (675104227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675104227:ℝ)/168755200)*ClassicalSixthBranch.v ((675104227:ℝ)/168755200)/ClassicalSixthBranch.r = (76269314248281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3934
  · change upperPayment 3935 ≤ upperValue ((point split endpoint 4096 3935+point split endpoint 4096 3936)/2)
    have hp : upperPayment 3935 = (26551636135:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3935+point split endpoint 4096 3936)/2 = (675129377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((675129377:ℝ)/168755200)*ClassicalSixthBranch.v ((675129377:ℝ)/168755200)/ClassicalSixthBranch.r = (76251261654737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3935
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_245
