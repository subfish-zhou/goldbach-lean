import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints189
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_189 (j : Fin 16) : upperPayment (16*189+j.val) ≤
    upperValue ((point split endpoint 4096 (16*189+j.val)+point split endpoint 4096 (16*189+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 3024 ≤ upperValue ((point split endpoint 4096 3024+point split endpoint 4096 3025)/2)
    have hp : upperPayment 3024 = (158307309493:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3024+point split endpoint 4096 3025)/2 = (652217727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652217727:ℝ)/168755200)*ClassicalSixthBranch.v ((652217727:ℝ)/168755200)/ClassicalSixthBranch.r = (93536162337681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3024
  · change upperPayment 3025 ≤ upperValue ((point split endpoint 4096 3025+point split endpoint 4096 3026)/2)
    have hp : upperPayment 3025 = (158178785930:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3025+point split endpoint 4096 3026)/2 = (652242877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652242877:ℝ)/168755200)*ClassicalSixthBranch.v ((652242877:ℝ)/168755200)/ClassicalSixthBranch.r = (93516267838617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3025
  · change upperPayment 3026 ≤ upperValue ((point split endpoint 4096 3026+point split endpoint 4096 3027)/2)
    have hp : upperPayment 3026 = (158050229582:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3026+point split endpoint 4096 3027)/2 = (652268027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652268027:ℝ)/168755200)*ClassicalSixthBranch.v ((652268027:ℝ)/168755200)/ClassicalSixthBranch.r = (93496375363625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3026
  · change upperPayment 3027 ≤ upperValue ((point split endpoint 4096 3027+point split endpoint 4096 3028)/2)
    have hp : upperPayment 3027 = (157921640441:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3027+point split endpoint 4096 3028)/2 = (652293177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652293177:ℝ)/168755200)*ClassicalSixthBranch.v ((652293177:ℝ)/168755200)/ClassicalSixthBranch.r = (93476484912705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3027
  · change upperPayment 3028 ≤ upperValue ((point split endpoint 4096 3028+point split endpoint 4096 3029)/2)
    have hp : upperPayment 3028 = (157793018498:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3028+point split endpoint 4096 3029)/2 = (652318327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652318327:ℝ)/168755200)*ClassicalSixthBranch.v ((652318327:ℝ)/168755200)/ClassicalSixthBranch.r = (93456596485857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3028
  · change upperPayment 3029 ≤ upperValue ((point split endpoint 4096 3029+point split endpoint 4096 3030)/2)
    have hp : upperPayment 3029 = (157664363746:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3029+point split endpoint 4096 3030)/2 = (652343477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652343477:ℝ)/168755200)*ClassicalSixthBranch.v ((652343477:ℝ)/168755200)/ClassicalSixthBranch.r = (93436710083081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3029
  · change upperPayment 3030 ≤ upperValue ((point split endpoint 4096 3030+point split endpoint 4096 3031)/2)
    have hp : upperPayment 3030 = (157535676177:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3030+point split endpoint 4096 3031)/2 = (652368627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652368627:ℝ)/168755200)*ClassicalSixthBranch.v ((652368627:ℝ)/168755200)/ClassicalSixthBranch.r = (93416825704377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3030
  · change upperPayment 3031 ≤ upperValue ((point split endpoint 4096 3031+point split endpoint 4096 3032)/2)
    have hp : upperPayment 3031 = (157406955783:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3031+point split endpoint 4096 3032)/2 = (652393777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652393777:ℝ)/168755200)*ClassicalSixthBranch.v ((652393777:ℝ)/168755200)/ClassicalSixthBranch.r = (93396943349745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3031
  · change upperPayment 3032 ≤ upperValue ((point split endpoint 4096 3032+point split endpoint 4096 3033)/2)
    have hp : upperPayment 3032 = (157278202557:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3032+point split endpoint 4096 3033)/2 = (652418927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652418927:ℝ)/168755200)*ClassicalSixthBranch.v ((652418927:ℝ)/168755200)/ClassicalSixthBranch.r = (93377063019185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3032
  · change upperPayment 3033 ≤ upperValue ((point split endpoint 4096 3033+point split endpoint 4096 3034)/2)
    have hp : upperPayment 3033 = (157149416490:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3033+point split endpoint 4096 3034)/2 = (652444077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652444077:ℝ)/168755200)*ClassicalSixthBranch.v ((652444077:ℝ)/168755200)/ClassicalSixthBranch.r = (93357184712697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3033
  · change upperPayment 3034 ≤ upperValue ((point split endpoint 4096 3034+point split endpoint 4096 3035)/2)
    have hp : upperPayment 3034 = (157020597575:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3034+point split endpoint 4096 3035)/2 = (652469227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652469227:ℝ)/168755200)*ClassicalSixthBranch.v ((652469227:ℝ)/168755200)/ClassicalSixthBranch.r = (93337308430281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3034
  · change upperPayment 3035 ≤ upperValue ((point split endpoint 4096 3035+point split endpoint 4096 3036)/2)
    have hp : upperPayment 3035 = (156891745804:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3035+point split endpoint 4096 3036)/2 = (652494377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652494377:ℝ)/168755200)*ClassicalSixthBranch.v ((652494377:ℝ)/168755200)/ClassicalSixthBranch.r = (93317434171937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3035
  · change upperPayment 3036 ≤ upperValue ((point split endpoint 4096 3036+point split endpoint 4096 3037)/2)
    have hp : upperPayment 3036 = (156762861168:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3036+point split endpoint 4096 3037)/2 = (652519527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652519527:ℝ)/168755200)*ClassicalSixthBranch.v ((652519527:ℝ)/168755200)/ClassicalSixthBranch.r = (93297561937665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3036
  · change upperPayment 3037 ≤ upperValue ((point split endpoint 4096 3037+point split endpoint 4096 3038)/2)
    have hp : upperPayment 3037 = (156633943661:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3037+point split endpoint 4096 3038)/2 = (652544677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652544677:ℝ)/168755200)*ClassicalSixthBranch.v ((652544677:ℝ)/168755200)/ClassicalSixthBranch.r = (93277691727465:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3037
  · change upperPayment 3038 ≤ upperValue ((point split endpoint 4096 3038+point split endpoint 4096 3039)/2)
    have hp : upperPayment 3038 = (156504993275:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3038+point split endpoint 4096 3039)/2 = (652569827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652569827:ℝ)/168755200)*ClassicalSixthBranch.v ((652569827:ℝ)/168755200)/ClassicalSixthBranch.r = (93257823541337:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3038
  · change upperPayment 3039 ≤ upperValue ((point split endpoint 4096 3039+point split endpoint 4096 3040)/2)
    have hp : upperPayment 3039 = (156376010000:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 3039+point split endpoint 4096 3040)/2 = (652594977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((652594977:ℝ)/168755200)*ClassicalSixthBranch.v ((652594977:ℝ)/168755200)/ClassicalSixthBranch.r = (93237957379281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_3039
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_189
