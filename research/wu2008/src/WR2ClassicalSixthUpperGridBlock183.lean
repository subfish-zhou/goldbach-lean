import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints183
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_183 (j : Fin 16) : upperPayment (16*183+j.val) ≤
    upperValue ((point split endpoint 4096 (16*183+j.val)+point split endpoint 4096 (16*183+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2928 ≤ upperValue ((point split endpoint 4096 2928+point split endpoint 4096 2929)/2)
    have hp : upperPayment 2928 = (170494099109:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2928+point split endpoint 4096 2929)/2 = (649803327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649803327:ℝ)/168755200)*ClassicalSixthBranch.v ((649803327:ℝ)/168755200)/ClassicalSixthBranch.r = (95455458327057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2928
  · change upperPayment 2929 ≤ upperValue ((point split endpoint 4096 2929+point split endpoint 4096 2930)/2)
    have hp : upperPayment 2929 = (170368687034:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2929+point split endpoint 4096 2930)/2 = (649828477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649828477:ℝ)/168755200)*ClassicalSixthBranch.v ((649828477:ℝ)/168755200)/ClassicalSixthBranch.r = (95435369517081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2929
  · change upperPayment 2930 ≤ upperValue ((point split endpoint 4096 2930+point split endpoint 4096 2931)/2)
    have hp : upperPayment 2930 = (170243242911:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2930+point split endpoint 4096 2931)/2 = (649853627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649853627:ℝ)/168755200)*ClassicalSixthBranch.v ((649853627:ℝ)/168755200)/ClassicalSixthBranch.r = (95415282731177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2930
  · change upperPayment 2931 ≤ upperValue ((point split endpoint 4096 2931+point split endpoint 4096 2932)/2)
    have hp : upperPayment 2931 = (170117766730:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2931+point split endpoint 4096 2932)/2 = (649878777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649878777:ℝ)/168755200)*ClassicalSixthBranch.v ((649878777:ℝ)/168755200)/ClassicalSixthBranch.r = (95395197969345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2931
  · change upperPayment 2932 ≤ upperValue ((point split endpoint 4096 2932+point split endpoint 4096 2933)/2)
    have hp : upperPayment 2932 = (169992258485:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2932+point split endpoint 4096 2933)/2 = (649903927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649903927:ℝ)/168755200)*ClassicalSixthBranch.v ((649903927:ℝ)/168755200)/ClassicalSixthBranch.r = (95375115231585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2932
  · change upperPayment 2933 ≤ upperValue ((point split endpoint 4096 2933+point split endpoint 4096 2934)/2)
    have hp : upperPayment 2933 = (169866718167:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2933+point split endpoint 4096 2934)/2 = (649929077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649929077:ℝ)/168755200)*ClassicalSixthBranch.v ((649929077:ℝ)/168755200)/ClassicalSixthBranch.r = (95355034517897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2933
  · change upperPayment 2934 ≤ upperValue ((point split endpoint 4096 2934+point split endpoint 4096 2935)/2)
    have hp : upperPayment 2934 = (169741145771:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2934+point split endpoint 4096 2935)/2 = (649954227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649954227:ℝ)/168755200)*ClassicalSixthBranch.v ((649954227:ℝ)/168755200)/ClassicalSixthBranch.r = (95334955828281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2934
  · change upperPayment 2935 ≤ upperValue ((point split endpoint 4096 2935+point split endpoint 4096 2936)/2)
    have hp : upperPayment 2935 = (169615541287:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2935+point split endpoint 4096 2936)/2 = (649979377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((649979377:ℝ)/168755200)*ClassicalSixthBranch.v ((649979377:ℝ)/168755200)/ClassicalSixthBranch.r = (95314879162737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2935
  · change upperPayment 2936 ≤ upperValue ((point split endpoint 4096 2936+point split endpoint 4096 2937)/2)
    have hp : upperPayment 2936 = (169489904708:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2936+point split endpoint 4096 2937)/2 = (650004527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650004527:ℝ)/168755200)*ClassicalSixthBranch.v ((650004527:ℝ)/168755200)/ClassicalSixthBranch.r = (95294804521265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2936
  · change upperPayment 2937 ≤ upperValue ((point split endpoint 4096 2937+point split endpoint 4096 2938)/2)
    have hp : upperPayment 2937 = (169364236027:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2937+point split endpoint 4096 2938)/2 = (650029677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650029677:ℝ)/168755200)*ClassicalSixthBranch.v ((650029677:ℝ)/168755200)/ClassicalSixthBranch.r = (95274731903865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2937
  · change upperPayment 2938 ≤ upperValue ((point split endpoint 4096 2938+point split endpoint 4096 2939)/2)
    have hp : upperPayment 2938 = (169238535237:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2938+point split endpoint 4096 2939)/2 = (650054827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650054827:ℝ)/168755200)*ClassicalSixthBranch.v ((650054827:ℝ)/168755200)/ClassicalSixthBranch.r = (95254661310537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2938
  · change upperPayment 2939 ≤ upperValue ((point split endpoint 4096 2939+point split endpoint 4096 2940)/2)
    have hp : upperPayment 2939 = (169112802329:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2939+point split endpoint 4096 2940)/2 = (650079977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650079977:ℝ)/168755200)*ClassicalSixthBranch.v ((650079977:ℝ)/168755200)/ClassicalSixthBranch.r = (95234592741281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2939
  · change upperPayment 2940 ≤ upperValue ((point split endpoint 4096 2940+point split endpoint 4096 2941)/2)
    have hp : upperPayment 2940 = (168987037297:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2940+point split endpoint 4096 2941)/2 = (650105127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650105127:ℝ)/168755200)*ClassicalSixthBranch.v ((650105127:ℝ)/168755200)/ClassicalSixthBranch.r = (95214526196097:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2940
  · change upperPayment 2941 ≤ upperValue ((point split endpoint 4096 2941+point split endpoint 4096 2942)/2)
    have hp : upperPayment 2941 = (168861240132:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2941+point split endpoint 4096 2942)/2 = (650130277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650130277:ℝ)/168755200)*ClassicalSixthBranch.v ((650130277:ℝ)/168755200)/ClassicalSixthBranch.r = (95194461674985:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2941
  · change upperPayment 2942 ≤ upperValue ((point split endpoint 4096 2942+point split endpoint 4096 2943)/2)
    have hp : upperPayment 2942 = (168735410827:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2942+point split endpoint 4096 2943)/2 = (650155427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650155427:ℝ)/168755200)*ClassicalSixthBranch.v ((650155427:ℝ)/168755200)/ClassicalSixthBranch.r = (95174399177945:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2942
  · change upperPayment 2943 ≤ upperValue ((point split endpoint 4096 2943+point split endpoint 4096 2944)/2)
    have hp : upperPayment 2943 = (168609549374:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2943+point split endpoint 4096 2944)/2 = (650180577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650180577:ℝ)/168755200)*ClassicalSixthBranch.v ((650180577:ℝ)/168755200)/ClassicalSixthBranch.r = (95154338704977:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2943
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_183
