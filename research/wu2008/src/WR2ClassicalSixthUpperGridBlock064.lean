import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints064
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_064 (j : Fin 16) : upperPayment (16*64+j.val) ≤
    upperValue ((point split endpoint 4096 (16*64+j.val)+point split endpoint 4096 (16*64+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 1024 ≤ upperValue ((point split endpoint 4096 1024+point split endpoint 4096 1025)/2)
    have hp : upperPayment 1024 = (358383400963:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1024+point split endpoint 4096 1025)/2 = (601917727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601917727:ℝ)/168755200)*ClassicalSixthBranch.v ((601917727:ℝ)/168755200)/ClassicalSixthBranch.r = (137375328537681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1024
  · change upperPayment 1025 ≤ upperValue ((point split endpoint 4096 1025+point split endpoint 4096 1026)/2)
    have hp : upperPayment 1025 = (358308284027:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1025+point split endpoint 4096 1026)/2 = (601942877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601942877:ℝ)/168755200)*ClassicalSixthBranch.v ((601942877:ℝ)/168755200)/ClassicalSixthBranch.r = (137351385894617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1025
  · change upperPayment 1026 ≤ upperValue ((point split endpoint 4096 1026+point split endpoint 4096 1027)/2)
    have hp : upperPayment 1026 = (358233145028:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1026+point split endpoint 4096 1027)/2 = (601968027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601968027:ℝ)/168755200)*ClassicalSixthBranch.v ((601968027:ℝ)/168755200)/ClassicalSixthBranch.r = (137327445275625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1026
  · change upperPayment 1027 ≤ upperValue ((point split endpoint 4096 1027+point split endpoint 4096 1028)/2)
    have hp : upperPayment 1027 = (358157983963:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1027+point split endpoint 4096 1028)/2 = (601993177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((601993177:ℝ)/168755200)*ClassicalSixthBranch.v ((601993177:ℝ)/168755200)/ClassicalSixthBranch.r = (137303506680705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1027
  · change upperPayment 1028 ≤ upperValue ((point split endpoint 4096 1028+point split endpoint 4096 1029)/2)
    have hp : upperPayment 1028 = (358082800829:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1028+point split endpoint 4096 1029)/2 = (602018327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602018327:ℝ)/168755200)*ClassicalSixthBranch.v ((602018327:ℝ)/168755200)/ClassicalSixthBranch.r = (137279570109857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1028
  · change upperPayment 1029 ≤ upperValue ((point split endpoint 4096 1029+point split endpoint 4096 1030)/2)
    have hp : upperPayment 1029 = (358007595622:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1029+point split endpoint 4096 1030)/2 = (602043477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602043477:ℝ)/168755200)*ClassicalSixthBranch.v ((602043477:ℝ)/168755200)/ClassicalSixthBranch.r = (137255635563081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1029
  · change upperPayment 1030 ≤ upperValue ((point split endpoint 4096 1030+point split endpoint 4096 1031)/2)
    have hp : upperPayment 1030 = (357932368339:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1030+point split endpoint 4096 1031)/2 = (602068627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602068627:ℝ)/168755200)*ClassicalSixthBranch.v ((602068627:ℝ)/168755200)/ClassicalSixthBranch.r = (137231703040377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1030
  · change upperPayment 1031 ≤ upperValue ((point split endpoint 4096 1031+point split endpoint 4096 1032)/2)
    have hp : upperPayment 1031 = (357857118976:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1031+point split endpoint 4096 1032)/2 = (602093777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602093777:ℝ)/168755200)*ClassicalSixthBranch.v ((602093777:ℝ)/168755200)/ClassicalSixthBranch.r = (137207772541745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1031
  · change upperPayment 1032 ≤ upperValue ((point split endpoint 4096 1032+point split endpoint 4096 1033)/2)
    have hp : upperPayment 1032 = (357781847530:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1032+point split endpoint 4096 1033)/2 = (602118927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602118927:ℝ)/168755200)*ClassicalSixthBranch.v ((602118927:ℝ)/168755200)/ClassicalSixthBranch.r = (137183844067185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1032
  · change upperPayment 1033 ≤ upperValue ((point split endpoint 4096 1033+point split endpoint 4096 1034)/2)
    have hp : upperPayment 1033 = (357706553997:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1033+point split endpoint 4096 1034)/2 = (5846059:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((5846059:ℝ)/1638400)*ClassicalSixthBranch.v ((5846059:ℝ)/1638400)/ClassicalSixthBranch.r = (1331649685599:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1033
  · change upperPayment 1034 ≤ upperValue ((point split endpoint 4096 1034+point split endpoint 4096 1035)/2)
    have hp : upperPayment 1034 = (357631238374:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1034+point split endpoint 4096 1035)/2 = (602169227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602169227:ℝ)/168755200)*ClassicalSixthBranch.v ((602169227:ℝ)/168755200)/ClassicalSixthBranch.r = (137135993190281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1034
  · change upperPayment 1035 ≤ upperValue ((point split endpoint 4096 1035+point split endpoint 4096 1036)/2)
    have hp : upperPayment 1035 = (357555900658:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1035+point split endpoint 4096 1036)/2 = (602194377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602194377:ℝ)/168755200)*ClassicalSixthBranch.v ((602194377:ℝ)/168755200)/ClassicalSixthBranch.r = (137112070787937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1035
  · change upperPayment 1036 ≤ upperValue ((point split endpoint 4096 1036+point split endpoint 4096 1037)/2)
    have hp : upperPayment 1036 = (357480540845:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1036+point split endpoint 4096 1037)/2 = (602219527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602219527:ℝ)/168755200)*ClassicalSixthBranch.v ((602219527:ℝ)/168755200)/ClassicalSixthBranch.r = (137088150409665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1036
  · change upperPayment 1037 ≤ upperValue ((point split endpoint 4096 1037+point split endpoint 4096 1038)/2)
    have hp : upperPayment 1037 = (357405158931:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1037+point split endpoint 4096 1038)/2 = (602244677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602244677:ℝ)/168755200)*ClassicalSixthBranch.v ((602244677:ℝ)/168755200)/ClassicalSixthBranch.r = (137064232055465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1037
  · change upperPayment 1038 ≤ upperValue ((point split endpoint 4096 1038+point split endpoint 4096 1039)/2)
    have hp : upperPayment 1038 = (357329754913:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1038+point split endpoint 4096 1039)/2 = (602269827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602269827:ℝ)/168755200)*ClassicalSixthBranch.v ((602269827:ℝ)/168755200)/ClassicalSixthBranch.r = (137040315725337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1038
  · change upperPayment 1039 ≤ upperValue ((point split endpoint 4096 1039+point split endpoint 4096 1040)/2)
    have hp : upperPayment 1039 = (357254328787:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 1039+point split endpoint 4096 1040)/2 = (602294977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((602294977:ℝ)/168755200)*ClassicalSixthBranch.v ((602294977:ℝ)/168755200)/ClassicalSixthBranch.r = (137016401419281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_1039
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_064
