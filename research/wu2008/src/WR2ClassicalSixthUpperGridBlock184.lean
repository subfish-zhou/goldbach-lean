import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints184
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_184 (j : Fin 16) : upperPayment (16*184+j.val) ≤
    upperValue ((point split endpoint 4096 (16*184+j.val)+point split endpoint 4096 (16*184+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2944 ≤ upperValue ((point split endpoint 4096 2944+point split endpoint 4096 2945)/2)
    have hp : upperPayment 2944 = (168483655767:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2944+point split endpoint 4096 2945)/2 = (650205727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650205727:ℝ)/168755200)*ClassicalSixthBranch.v ((650205727:ℝ)/168755200)/ClassicalSixthBranch.r = (95134280256081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2944
  · change upperPayment 2945 ≤ upperValue ((point split endpoint 4096 2945+point split endpoint 4096 2946)/2)
    have hp : upperPayment 2945 = (168357729997:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2945+point split endpoint 4096 2946)/2 = (650230877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650230877:ℝ)/168755200)*ClassicalSixthBranch.v ((650230877:ℝ)/168755200)/ClassicalSixthBranch.r = (95114223831257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2945
  · change upperPayment 2946 ≤ upperValue ((point split endpoint 4096 2946+point split endpoint 4096 2947)/2)
    have hp : upperPayment 2946 = (168231772057:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2946+point split endpoint 4096 2947)/2 = (650256027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650256027:ℝ)/168755200)*ClassicalSixthBranch.v ((650256027:ℝ)/168755200)/ClassicalSixthBranch.r = (95094169430505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2946
  · change upperPayment 2947 ≤ upperValue ((point split endpoint 4096 2947+point split endpoint 4096 2948)/2)
    have hp : upperPayment 2947 = (168105781939:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2947+point split endpoint 4096 2948)/2 = (650281177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650281177:ℝ)/168755200)*ClassicalSixthBranch.v ((650281177:ℝ)/168755200)/ClassicalSixthBranch.r = (95074117053825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2947
  · change upperPayment 2948 ≤ upperValue ((point split endpoint 4096 2948+point split endpoint 4096 2949)/2)
    have hp : upperPayment 2948 = (167979759636:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2948+point split endpoint 4096 2949)/2 = (650306327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650306327:ℝ)/168755200)*ClassicalSixthBranch.v ((650306327:ℝ)/168755200)/ClassicalSixthBranch.r = (95054066701217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2948
  · change upperPayment 2949 ≤ upperValue ((point split endpoint 4096 2949+point split endpoint 4096 2950)/2)
    have hp : upperPayment 2949 = (167853705140:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2949+point split endpoint 4096 2950)/2 = (650331477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650331477:ℝ)/168755200)*ClassicalSixthBranch.v ((650331477:ℝ)/168755200)/ClassicalSixthBranch.r = (95034018372681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2949
  · change upperPayment 2950 ≤ upperValue ((point split endpoint 4096 2950+point split endpoint 4096 2951)/2)
    have hp : upperPayment 2950 = (167727618443:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2950+point split endpoint 4096 2951)/2 = (650356627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650356627:ℝ)/168755200)*ClassicalSixthBranch.v ((650356627:ℝ)/168755200)/ClassicalSixthBranch.r = (95013972068217:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2950
  · change upperPayment 2951 ≤ upperValue ((point split endpoint 4096 2951+point split endpoint 4096 2952)/2)
    have hp : upperPayment 2951 = (167601499538:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2951+point split endpoint 4096 2952)/2 = (650381777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650381777:ℝ)/168755200)*ClassicalSixthBranch.v ((650381777:ℝ)/168755200)/ClassicalSixthBranch.r = (94993927787825:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2951
  · change upperPayment 2952 ≤ upperValue ((point split endpoint 4096 2952+point split endpoint 4096 2953)/2)
    have hp : upperPayment 2952 = (167475348418:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2952+point split endpoint 4096 2953)/2 = (650406927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650406927:ℝ)/168755200)*ClassicalSixthBranch.v ((650406927:ℝ)/168755200)/ClassicalSixthBranch.r = (94973885531505:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2952
  · change upperPayment 2953 ≤ upperValue ((point split endpoint 4096 2953+point split endpoint 4096 2954)/2)
    have hp : upperPayment 2953 = (167349165074:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2953+point split endpoint 4096 2954)/2 = (650432077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650432077:ℝ)/168755200)*ClassicalSixthBranch.v ((650432077:ℝ)/168755200)/ClassicalSixthBranch.r = (94953845299257:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2953
  · change upperPayment 2954 ≤ upperValue ((point split endpoint 4096 2954+point split endpoint 4096 2955)/2)
    have hp : upperPayment 2954 = (167222949500:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2954+point split endpoint 4096 2955)/2 = (650457227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650457227:ℝ)/168755200)*ClassicalSixthBranch.v ((650457227:ℝ)/168755200)/ClassicalSixthBranch.r = (94933807091081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2954
  · change upperPayment 2955 ≤ upperValue ((point split endpoint 4096 2955+point split endpoint 4096 2956)/2)
    have hp : upperPayment 2955 = (167096701687:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2955+point split endpoint 4096 2956)/2 = (650482377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650482377:ℝ)/168755200)*ClassicalSixthBranch.v ((650482377:ℝ)/168755200)/ClassicalSixthBranch.r = (94913770906977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2955
  · change upperPayment 2956 ≤ upperValue ((point split endpoint 4096 2956+point split endpoint 4096 2957)/2)
    have hp : upperPayment 2956 = (166970421628:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2956+point split endpoint 4096 2957)/2 = (650507527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650507527:ℝ)/168755200)*ClassicalSixthBranch.v ((650507527:ℝ)/168755200)/ClassicalSixthBranch.r = (94893736746945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2956
  · change upperPayment 2957 ≤ upperValue ((point split endpoint 4096 2957+point split endpoint 4096 2958)/2)
    have hp : upperPayment 2957 = (166844109315:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2957+point split endpoint 4096 2958)/2 = (650532677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650532677:ℝ)/168755200)*ClassicalSixthBranch.v ((650532677:ℝ)/168755200)/ClassicalSixthBranch.r = (94873704610985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2957
  · change upperPayment 2958 ≤ upperValue ((point split endpoint 4096 2958+point split endpoint 4096 2959)/2)
    have hp : upperPayment 2958 = (166717764742:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2958+point split endpoint 4096 2959)/2 = (650557827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650557827:ℝ)/168755200)*ClassicalSixthBranch.v ((650557827:ℝ)/168755200)/ClassicalSixthBranch.r = (94853674499097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2958
  · change upperPayment 2959 ≤ upperValue ((point split endpoint 4096 2959+point split endpoint 4096 2960)/2)
    have hp : upperPayment 2959 = (166591387899:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2959+point split endpoint 4096 2960)/2 = (650582977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650582977:ℝ)/168755200)*ClassicalSixthBranch.v ((650582977:ℝ)/168755200)/ClassicalSixthBranch.r = (94833646411281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2959
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_184
