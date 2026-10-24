import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints055
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_055 (j : Fin 16) : upperPayment (16*55+j.val) ≤
    upperValue ((point split endpoint 4096 (16*55+j.val)+point split endpoint 4096 (16*55+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 880 ≤ upperValue ((point split endpoint 4096 880+point split endpoint 4096 881)/2)
    have hp : upperPayment 880 = (368971632633:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 880+point split endpoint 4096 881)/2 = (598296127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598296127:ℝ)/168755200)*ClassicalSixthBranch.v ((598296127:ℝ)/168755200)/ClassicalSixthBranch.r = (140844200450577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_880
  · change upperPayment 881 ≤ upperValue ((point split endpoint 4096 881+point split endpoint 4096 882)/2)
    have hp : upperPayment 881 = (368899657431:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 881+point split endpoint 4096 882)/2 = (598321277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598321277:ℝ)/168755200)*ClassicalSixthBranch.v ((598321277:ℝ)/168755200)/ClassicalSixthBranch.r = (140819966341145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_881
  · change upperPayment 882 ≤ upperValue ((point split endpoint 4096 882+point split endpoint 4096 883)/2)
    have hp : upperPayment 882 = (368827660648:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 882+point split endpoint 4096 883)/2 = (598346427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598346427:ℝ)/168755200)*ClassicalSixthBranch.v ((598346427:ℝ)/168755200)/ClassicalSixthBranch.r = (140795734255785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_882
  · change upperPayment 883 ≤ upperValue ((point split endpoint 4096 883+point split endpoint 4096 884)/2)
    have hp : upperPayment 883 = (368755642280:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 883+point split endpoint 4096 884)/2 = (598371577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598371577:ℝ)/168755200)*ClassicalSixthBranch.v ((598371577:ℝ)/168755200)/ClassicalSixthBranch.r = (140771504194497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_883
  · change upperPayment 884 ≤ upperValue ((point split endpoint 4096 884+point split endpoint 4096 885)/2)
    have hp : upperPayment 884 = (368683602325:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 884+point split endpoint 4096 885)/2 = (598396727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598396727:ℝ)/168755200)*ClassicalSixthBranch.v ((598396727:ℝ)/168755200)/ClassicalSixthBranch.r = (140747276157281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_884
  · change upperPayment 885 ≤ upperValue ((point split endpoint 4096 885+point split endpoint 4096 886)/2)
    have hp : upperPayment 885 = (368611540779:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 885+point split endpoint 4096 886)/2 = (598421877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598421877:ℝ)/168755200)*ClassicalSixthBranch.v ((598421877:ℝ)/168755200)/ClassicalSixthBranch.r = (140723050144137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_885
  · change upperPayment 886 ≤ upperValue ((point split endpoint 4096 886+point split endpoint 4096 887)/2)
    have hp : upperPayment 886 = (368539457639:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 886+point split endpoint 4096 887)/2 = (598447027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598447027:ℝ)/168755200)*ClassicalSixthBranch.v ((598447027:ℝ)/168755200)/ClassicalSixthBranch.r = (140698826155065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_886
  · change upperPayment 887 ≤ upperValue ((point split endpoint 4096 887+point split endpoint 4096 888)/2)
    have hp : upperPayment 887 = (368467352901:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 887+point split endpoint 4096 888)/2 = (598472177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598472177:ℝ)/168755200)*ClassicalSixthBranch.v ((598472177:ℝ)/168755200)/ClassicalSixthBranch.r = (140674604190065:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_887
  · change upperPayment 888 ≤ upperValue ((point split endpoint 4096 888+point split endpoint 4096 889)/2)
    have hp : upperPayment 888 = (368395226563:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 888+point split endpoint 4096 889)/2 = (598497327:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598497327:ℝ)/168755200)*ClassicalSixthBranch.v ((598497327:ℝ)/168755200)/ClassicalSixthBranch.r = (140650384249137:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_888
  · change upperPayment 889 ≤ upperValue ((point split endpoint 4096 889+point split endpoint 4096 890)/2)
    have hp : upperPayment 889 = (368323078620:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 889+point split endpoint 4096 890)/2 = (598522477:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598522477:ℝ)/168755200)*ClassicalSixthBranch.v ((598522477:ℝ)/168755200)/ClassicalSixthBranch.r = (140626166332281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_889
  · change upperPayment 890 ≤ upperValue ((point split endpoint 4096 890+point split endpoint 4096 891)/2)
    have hp : upperPayment 890 = (368250909071:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 890+point split endpoint 4096 891)/2 = (598547627:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598547627:ℝ)/168755200)*ClassicalSixthBranch.v ((598547627:ℝ)/168755200)/ClassicalSixthBranch.r = (140601950439497:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_890
  · change upperPayment 891 ≤ upperValue ((point split endpoint 4096 891+point split endpoint 4096 892)/2)
    have hp : upperPayment 891 = (368178717912:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 891+point split endpoint 4096 892)/2 = (598572777:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598572777:ℝ)/168755200)*ClassicalSixthBranch.v ((598572777:ℝ)/168755200)/ClassicalSixthBranch.r = (140577736570785:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_891
  · change upperPayment 892 ≤ upperValue ((point split endpoint 4096 892+point split endpoint 4096 893)/2)
    have hp : upperPayment 892 = (368106505138:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 892+point split endpoint 4096 893)/2 = (598597927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598597927:ℝ)/168755200)*ClassicalSixthBranch.v ((598597927:ℝ)/168755200)/ClassicalSixthBranch.r = (140553524726145:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_892
  · change upperPayment 893 ≤ upperValue ((point split endpoint 4096 893+point split endpoint 4096 894)/2)
    have hp : upperPayment 893 = (368034270748:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 893+point split endpoint 4096 894)/2 = (598623077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598623077:ℝ)/168755200)*ClassicalSixthBranch.v ((598623077:ℝ)/168755200)/ClassicalSixthBranch.r = (140529314905577:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_893
  · change upperPayment 894 ≤ upperValue ((point split endpoint 4096 894+point split endpoint 4096 895)/2)
    have hp : upperPayment 894 = (367962014738:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 894+point split endpoint 4096 895)/2 = (598648227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598648227:ℝ)/168755200)*ClassicalSixthBranch.v ((598648227:ℝ)/168755200)/ClassicalSixthBranch.r = (140505107109081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_894
  · change upperPayment 895 ≤ upperValue ((point split endpoint 4096 895+point split endpoint 4096 896)/2)
    have hp : upperPayment 895 = (367889737104:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 895+point split endpoint 4096 896)/2 = (598673377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((598673377:ℝ)/168755200)*ClassicalSixthBranch.v ((598673377:ℝ)/168755200)/ClassicalSixthBranch.r = (140480901336657:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_895
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_055
