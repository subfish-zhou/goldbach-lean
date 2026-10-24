import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints059
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_059 (j : Fin 16) : upperPayment (16*59+j.val) ≤
    upperValue ((point split endpoint 4096 (16*59+j.val)+point split endpoint 4096 (16*59+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 944 ≤ upperValue ((point split endpoint 4096 944+point split endpoint 4096 945)/2)
    have hp : upperPayment 944 = (364321576253:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 944+point split endpoint 4096 945)/2 = (599905727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599905727:ℝ)/168755200)*ClassicalSixthBranch.v ((599905727:ℝ)/168755200)/ClassicalSixthBranch.r = (139297297976081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_944
  · change upperPayment 945 ≤ upperValue ((point split endpoint 4096 945+point split endpoint 4096 946)/2)
    have hp : upperPayment 945 = (364248213269:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 945+point split endpoint 4096 946)/2 = (599930877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599930877:ℝ)/168755200)*ClassicalSixthBranch.v ((599930877:ℝ)/168755200)/ClassicalSixthBranch.r = (139273193407257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_945
  · change upperPayment 946 ≤ upperValue ((point split endpoint 4096 946+point split endpoint 4096 947)/2)
    have hp : upperPayment 946 = (364174828493:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 946+point split endpoint 4096 947)/2 = (599956027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599956027:ℝ)/168755200)*ClassicalSixthBranch.v ((599956027:ℝ)/168755200)/ClassicalSixthBranch.r = (139249090862505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_946
  · change upperPayment 947 ≤ upperValue ((point split endpoint 4096 947+point split endpoint 4096 948)/2)
    have hp : upperPayment 947 = (364101421923:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 947+point split endpoint 4096 948)/2 = (599981177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((599981177:ℝ)/168755200)*ClassicalSixthBranch.v ((599981177:ℝ)/168755200)/ClassicalSixthBranch.r = (139224990341825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_947
  · change upperPayment 948 ≤ upperValue ((point split endpoint 4096 948+point split endpoint 4096 949)/2)
    have hp : upperPayment 948 = (364027993555:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 948+point split endpoint 4096 949)/2 = (600006327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600006327:ℝ)/168755200)*ClassicalSixthBranch.v ((600006327:ℝ)/168755200)/ClassicalSixthBranch.r = (139200891845217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_948
  · change upperPayment 949 ≤ upperValue ((point split endpoint 4096 949+point split endpoint 4096 950)/2)
    have hp : upperPayment 949 = (363954543385:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 949+point split endpoint 4096 950)/2 = (600031477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600031477:ℝ)/168755200)*ClassicalSixthBranch.v ((600031477:ℝ)/168755200)/ClassicalSixthBranch.r = (139176795372681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_949
  · change upperPayment 950 ≤ upperValue ((point split endpoint 4096 950+point split endpoint 4096 951)/2)
    have hp : upperPayment 950 = (363881071411:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 950+point split endpoint 4096 951)/2 = (600056627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600056627:ℝ)/168755200)*ClassicalSixthBranch.v ((600056627:ℝ)/168755200)/ClassicalSixthBranch.r = (139152700924217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_950
  · change upperPayment 951 ≤ upperValue ((point split endpoint 4096 951+point split endpoint 4096 952)/2)
    have hp : upperPayment 951 = (363807577629:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 951+point split endpoint 4096 952)/2 = (600081777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600081777:ℝ)/168755200)*ClassicalSixthBranch.v ((600081777:ℝ)/168755200)/ClassicalSixthBranch.r = (139128608499825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_951
  · change upperPayment 952 ≤ upperValue ((point split endpoint 4096 952+point split endpoint 4096 953)/2)
    have hp : upperPayment 952 = (363734062035:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 952+point split endpoint 4096 953)/2 = (600106927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600106927:ℝ)/168755200)*ClassicalSixthBranch.v ((600106927:ℝ)/168755200)/ClassicalSixthBranch.r = (139104518099505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_952
  · change upperPayment 953 ≤ upperValue ((point split endpoint 4096 953+point split endpoint 4096 954)/2)
    have hp : upperPayment 953 = (363660524627:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 953+point split endpoint 4096 954)/2 = (600132077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600132077:ℝ)/168755200)*ClassicalSixthBranch.v ((600132077:ℝ)/168755200)/ClassicalSixthBranch.r = (139080429723257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_953
  · change upperPayment 954 ≤ upperValue ((point split endpoint 4096 954+point split endpoint 4096 955)/2)
    have hp : upperPayment 954 = (363586965401:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 954+point split endpoint 4096 955)/2 = (600157227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600157227:ℝ)/168755200)*ClassicalSixthBranch.v ((600157227:ℝ)/168755200)/ClassicalSixthBranch.r = (1350061586127:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_954
  · change upperPayment 955 ≤ upperValue ((point split endpoint 4096 955+point split endpoint 4096 956)/2)
    have hp : upperPayment 955 = (363513384354:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 955+point split endpoint 4096 956)/2 = (600182377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600182377:ℝ)/168755200)*ClassicalSixthBranch.v ((600182377:ℝ)/168755200)/ClassicalSixthBranch.r = (139032259042977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_955
  · change upperPayment 956 ≤ upperValue ((point split endpoint 4096 956+point split endpoint 4096 957)/2)
    have hp : upperPayment 956 = (363439781481:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 956+point split endpoint 4096 957)/2 = (600207527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600207527:ℝ)/168755200)*ClassicalSixthBranch.v ((600207527:ℝ)/168755200)/ClassicalSixthBranch.r = (139008176738945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_956
  · change upperPayment 957 ≤ upperValue ((point split endpoint 4096 957+point split endpoint 4096 958)/2)
    have hp : upperPayment 957 = (363366156781:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 957+point split endpoint 4096 958)/2 = (600232677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600232677:ℝ)/168755200)*ClassicalSixthBranch.v ((600232677:ℝ)/168755200)/ClassicalSixthBranch.r = (138984096458985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_957
  · change upperPayment 958 ≤ upperValue ((point split endpoint 4096 958+point split endpoint 4096 959)/2)
    have hp : upperPayment 958 = (363292510250:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 958+point split endpoint 4096 959)/2 = (600257827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600257827:ℝ)/168755200)*ClassicalSixthBranch.v ((600257827:ℝ)/168755200)/ClassicalSixthBranch.r = (138960018203097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_958
  · change upperPayment 959 ≤ upperValue ((point split endpoint 4096 959+point split endpoint 4096 960)/2)
    have hp : upperPayment 959 = (363218841883:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 959+point split endpoint 4096 960)/2 = (600282977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((600282977:ℝ)/168755200)*ClassicalSixthBranch.v ((600282977:ℝ)/168755200)/ClassicalSixthBranch.r = (138935941971281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_959
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_059
