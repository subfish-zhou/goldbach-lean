import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints180
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_180 (j : Fin 16) : upperPayment (16*180+j.val) ≤
    upperValue ((point split endpoint 4096 (16*180+j.val)+point split endpoint 4096 (16*180+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 2880 ≤ upperValue ((point split endpoint 4096 2880+point split endpoint 4096 2881)/2)
    have hp : upperPayment 2880 = (176476335174:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2880+point split endpoint 4096 2881)/2 = (648596127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648596127:ℝ)/168755200)*ClassicalSixthBranch.v ((648596127:ℝ)/168755200)/ClassicalSixthBranch.r = (96422101514577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2880
  · change upperPayment 2881 ≤ upperValue ((point split endpoint 4096 2881+point split endpoint 4096 2882)/2)
    have hp : upperPayment 2881 = (176352452687:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2881+point split endpoint 4096 2882)/2 = (648621277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648621277:ℝ)/168755200)*ClassicalSixthBranch.v ((648621277:ℝ)/168755200)/ClassicalSixthBranch.r = (96401915549145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2881
  · change upperPayment 2882 ≤ upperValue ((point split endpoint 4096 2882+point split endpoint 4096 2883)/2)
    have hp : upperPayment 2882 = (176228538509:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2882+point split endpoint 4096 2883)/2 = (648646427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648646427:ℝ)/168755200)*ClassicalSixthBranch.v ((648646427:ℝ)/168755200)/ClassicalSixthBranch.r = (96381731607785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2882
  · change upperPayment 2883 ≤ upperValue ((point split endpoint 4096 2883+point split endpoint 4096 2884)/2)
    have hp : upperPayment 2883 = (176104592631:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2883+point split endpoint 4096 2884)/2 = (648671577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648671577:ℝ)/168755200)*ClassicalSixthBranch.v ((648671577:ℝ)/168755200)/ClassicalSixthBranch.r = (96361549690497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2883
  · change upperPayment 2884 ≤ upperValue ((point split endpoint 4096 2884+point split endpoint 4096 2885)/2)
    have hp : upperPayment 2884 = (175980615047:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2884+point split endpoint 4096 2885)/2 = (648696727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648696727:ℝ)/168755200)*ClassicalSixthBranch.v ((648696727:ℝ)/168755200)/ClassicalSixthBranch.r = (96341369797281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2884
  · change upperPayment 2885 ≤ upperValue ((point split endpoint 4096 2885+point split endpoint 4096 2886)/2)
    have hp : upperPayment 2885 = (175856605749:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2885+point split endpoint 4096 2886)/2 = (648721877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648721877:ℝ)/168755200)*ClassicalSixthBranch.v ((648721877:ℝ)/168755200)/ClassicalSixthBranch.r = (96321191928137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2885
  · change upperPayment 2886 ≤ upperValue ((point split endpoint 4096 2886+point split endpoint 4096 2887)/2)
    have hp : upperPayment 2886 = (175732564729:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2886+point split endpoint 4096 2887)/2 = (648747027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648747027:ℝ)/168755200)*ClassicalSixthBranch.v ((648747027:ℝ)/168755200)/ClassicalSixthBranch.r = (96301016083065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2886
  · change upperPayment 2887 ≤ upperValue ((point split endpoint 4096 2887+point split endpoint 4096 2888)/2)
    have hp : upperPayment 2887 = (175608491980:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2887+point split endpoint 4096 2888)/2 = (6298759:ℝ)/1638400 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((6298759:ℝ)/1638400)*ClassicalSixthBranch.v ((6298759:ℝ)/1638400)/ClassicalSixthBranch.r = (934765458855:ℝ)/712427700224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2887
  · change upperPayment 2888 ≤ upperValue ((point split endpoint 4096 2888+point split endpoint 4096 2889)/2)
    have hp : upperPayment 2888 = (175484387494:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2888+point split endpoint 4096 2889)/2 = (648797327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648797327:ℝ)/168755200)*ClassicalSixthBranch.v ((648797327:ℝ)/168755200)/ClassicalSixthBranch.r = (96260670465137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2888
  · change upperPayment 2889 ≤ upperValue ((point split endpoint 4096 2889+point split endpoint 4096 2890)/2)
    have hp : upperPayment 2889 = (175360251266:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2889+point split endpoint 4096 2890)/2 = (648822477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648822477:ℝ)/168755200)*ClassicalSixthBranch.v ((648822477:ℝ)/168755200)/ClassicalSixthBranch.r = (96240500692281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2889
  · change upperPayment 2890 ≤ upperValue ((point split endpoint 4096 2890+point split endpoint 4096 2891)/2)
    have hp : upperPayment 2890 = (175236083286:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2890+point split endpoint 4096 2891)/2 = (648847627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648847627:ℝ)/168755200)*ClassicalSixthBranch.v ((648847627:ℝ)/168755200)/ClassicalSixthBranch.r = (96220332943497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2890
  · change upperPayment 2891 ≤ upperValue ((point split endpoint 4096 2891+point split endpoint 4096 2892)/2)
    have hp : upperPayment 2891 = (175111883547:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2891+point split endpoint 4096 2892)/2 = (648872777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648872777:ℝ)/168755200)*ClassicalSixthBranch.v ((648872777:ℝ)/168755200)/ClassicalSixthBranch.r = (96200167218785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2891
  · change upperPayment 2892 ≤ upperValue ((point split endpoint 4096 2892+point split endpoint 4096 2893)/2)
    have hp : upperPayment 2892 = (174987652043:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2892+point split endpoint 4096 2893)/2 = (648897927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648897927:ℝ)/168755200)*ClassicalSixthBranch.v ((648897927:ℝ)/168755200)/ClassicalSixthBranch.r = (96180003518145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2892
  · change upperPayment 2893 ≤ upperValue ((point split endpoint 4096 2893+point split endpoint 4096 2894)/2)
    have hp : upperPayment 2893 = (174863388766:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2893+point split endpoint 4096 2894)/2 = (648923077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648923077:ℝ)/168755200)*ClassicalSixthBranch.v ((648923077:ℝ)/168755200)/ClassicalSixthBranch.r = (96159841841577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2893
  · change upperPayment 2894 ≤ upperValue ((point split endpoint 4096 2894+point split endpoint 4096 2895)/2)
    have hp : upperPayment 2894 = (174739093707:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2894+point split endpoint 4096 2895)/2 = (648948227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648948227:ℝ)/168755200)*ClassicalSixthBranch.v ((648948227:ℝ)/168755200)/ClassicalSixthBranch.r = (96139682189081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2894
  · change upperPayment 2895 ≤ upperValue ((point split endpoint 4096 2895+point split endpoint 4096 2896)/2)
    have hp : upperPayment 2895 = (174614766861:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 2895+point split endpoint 4096 2896)/2 = (648973377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((648973377:ℝ)/168755200)*ClassicalSixthBranch.v ((648973377:ℝ)/168755200)/ClassicalSixthBranch.r = (96119524560657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_2895
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_180
