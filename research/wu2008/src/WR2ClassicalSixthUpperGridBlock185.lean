import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints185
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_185 (j : Fin 16) : upperPayment (16*185+j.val) ≤
    upperValue ((point split endpoint 4096 (16*185+j.val)+point split endpoint 4096 (16*185+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2960 ≤ upperValue ((point split endpoint 4096 2960+point split endpoint 4096 2961)/2)
    have hp : upperPayment 2960 = (166464978780:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2960+point split endpoint 4096 2961)/2 = (650608127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650608127:ℝ)/168755200)*ClassicalSixthBranch.v ((650608127:ℝ)/168755200)/ClassicalSixthBranch.r = (94813620347537:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2960
  · change upperPayment 2961 ≤ upperValue ((point split endpoint 4096 2961+point split endpoint 4096 2962)/2)
    have hp : upperPayment 2961 = (166338537377:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2961+point split endpoint 4096 2962)/2 = (650633277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650633277:ℝ)/168755200)*ClassicalSixthBranch.v ((650633277:ℝ)/168755200)/ClassicalSixthBranch.r = (94793596307865:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2961
  · change upperPayment 2962 ≤ upperValue ((point split endpoint 4096 2962+point split endpoint 4096 2963)/2)
    have hp : upperPayment 2962 = (166212063682:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2962+point split endpoint 4096 2963)/2 = (650658427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650658427:ℝ)/168755200)*ClassicalSixthBranch.v ((650658427:ℝ)/168755200)/ClassicalSixthBranch.r = (94773574292265:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2962
  · change upperPayment 2963 ≤ upperValue ((point split endpoint 4096 2963+point split endpoint 4096 2964)/2)
    have hp : upperPayment 2963 = (166085557688:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2963+point split endpoint 4096 2964)/2 = (650683577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650683577:ℝ)/168755200)*ClassicalSixthBranch.v ((650683577:ℝ)/168755200)/ClassicalSixthBranch.r = (94753554300737:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2963
  · change upperPayment 2964 ≤ upperValue ((point split endpoint 4096 2964+point split endpoint 4096 2965)/2)
    have hp : upperPayment 2964 = (165959019387:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2964+point split endpoint 4096 2965)/2 = (650708727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650708727:ℝ)/168755200)*ClassicalSixthBranch.v ((650708727:ℝ)/168755200)/ClassicalSixthBranch.r = (94733536333281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2964
  · change upperPayment 2965 ≤ upperValue ((point split endpoint 4096 2965+point split endpoint 4096 2966)/2)
    have hp : upperPayment 2965 = (165832448771:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2965+point split endpoint 4096 2966)/2 = (650733877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650733877:ℝ)/168755200)*ClassicalSixthBranch.v ((650733877:ℝ)/168755200)/ClassicalSixthBranch.r = (94713520389897:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2965
  · change upperPayment 2966 ≤ upperValue ((point split endpoint 4096 2966+point split endpoint 4096 2967)/2)
    have hp : upperPayment 2966 = (165705845834:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2966+point split endpoint 4096 2967)/2 = (650759027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650759027:ℝ)/168755200)*ClassicalSixthBranch.v ((650759027:ℝ)/168755200)/ClassicalSixthBranch.r = (94693506470585:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2966
  · change upperPayment 2967 ≤ upperValue ((point split endpoint 4096 2967+point split endpoint 4096 2968)/2)
    have hp : upperPayment 2967 = (165579210566:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2967+point split endpoint 4096 2968)/2 = (650784177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650784177:ℝ)/168755200)*ClassicalSixthBranch.v ((650784177:ℝ)/168755200)/ClassicalSixthBranch.r = (94673494575345:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2967
  · change upperPayment 2968 ≤ upperValue ((point split endpoint 4096 2968+point split endpoint 4096 2969)/2)
    have hp : upperPayment 2968 = (165452542961:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2968+point split endpoint 4096 2969)/2 = (650809327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650809327:ℝ)/168755200)*ClassicalSixthBranch.v ((650809327:ℝ)/168755200)/ClassicalSixthBranch.r = (94653484704177:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2968
  · change upperPayment 2969 ≤ upperValue ((point split endpoint 4096 2969+point split endpoint 4096 2970)/2)
    have hp : upperPayment 2969 = (165325843011:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2969+point split endpoint 4096 2970)/2 = (650834477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650834477:ℝ)/168755200)*ClassicalSixthBranch.v ((650834477:ℝ)/168755200)/ClassicalSixthBranch.r = (94633476857081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2969
  · change upperPayment 2970 ≤ upperValue ((point split endpoint 4096 2970+point split endpoint 4096 2971)/2)
    have hp : upperPayment 2970 = (165199110708:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2970+point split endpoint 4096 2971)/2 = (650859627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650859627:ℝ)/168755200)*ClassicalSixthBranch.v ((650859627:ℝ)/168755200)/ClassicalSixthBranch.r = (94613471034057:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2970
  · change upperPayment 2971 ≤ upperValue ((point split endpoint 4096 2971+point split endpoint 4096 2972)/2)
    have hp : upperPayment 2971 = (165072346045:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2971+point split endpoint 4096 2972)/2 = (650884777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650884777:ℝ)/168755200)*ClassicalSixthBranch.v ((650884777:ℝ)/168755200)/ClassicalSixthBranch.r = (94593467235105:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2971
  · change upperPayment 2972 ≤ upperValue ((point split endpoint 4096 2972+point split endpoint 4096 2973)/2)
    have hp : upperPayment 2972 = (164945549013:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2972+point split endpoint 4096 2973)/2 = (650909927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650909927:ℝ)/168755200)*ClassicalSixthBranch.v ((650909927:ℝ)/168755200)/ClassicalSixthBranch.r = (94573465460225:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2972
  · change upperPayment 2973 ≤ upperValue ((point split endpoint 4096 2973+point split endpoint 4096 2974)/2)
    have hp : upperPayment 2973 = (164818719607:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2973+point split endpoint 4096 2974)/2 = (650935077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650935077:ℝ)/168755200)*ClassicalSixthBranch.v ((650935077:ℝ)/168755200)/ClassicalSixthBranch.r = (94553465709417:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2973
  · change upperPayment 2974 ≤ upperValue ((point split endpoint 4096 2974+point split endpoint 4096 2975)/2)
    have hp : upperPayment 2974 = (164691857816:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2974+point split endpoint 4096 2975)/2 = (650960227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650960227:ℝ)/168755200)*ClassicalSixthBranch.v ((650960227:ℝ)/168755200)/ClassicalSixthBranch.r = (94533467982681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2974
  · change upperPayment 2975 ≤ upperValue ((point split endpoint 4096 2975+point split endpoint 4096 2976)/2)
    have hp : upperPayment 2975 = (164564963635:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2975+point split endpoint 4096 2976)/2 = (650985377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((650985377:ℝ)/168755200)*ClassicalSixthBranch.v ((650985377:ℝ)/168755200)/ClassicalSixthBranch.r = (94513472280017:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2975
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_185
