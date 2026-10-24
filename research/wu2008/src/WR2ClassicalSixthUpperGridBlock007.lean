import WR2ClassicalSixthUpperPayments
import WR2ClassicalSixthUpperPoints007
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem upper_grid_block_007 (j : Fin 16) : upperPayment (16*7+j.val) ≤
    upperValue ((point split endpoint 4096 (16*7+j.val)+point split endpoint 4096 (16*7+j.val+1))/2) := by
  fin_cases j
  · change upperPayment 112 ≤ upperValue ((point split endpoint 4096 112+point split endpoint 4096 113)/2)
    have hp : upperPayment 112 = (418100961990:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 112+point split endpoint 4096 113)/2 = (578980927:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((578980927:ℝ)/168755200)*ClassicalSixthBranch.v ((578980927:ℝ)/168755200)/ClassicalSixthBranch.r = (160053696859665:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_112
  · change upperPayment 113 ≤ upperValue ((point split endpoint 4096 113+point split endpoint 4096 114)/2)
    have hp : upperPayment 113 = (418044708748:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 113+point split endpoint 4096 114)/2 = (579006077:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579006077:ℝ)/168755200)*ClassicalSixthBranch.v ((579006077:ℝ)/168755200)/ClassicalSixthBranch.r = (160027908262937:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_113
  · change upperPayment 114 ≤ upperValue ((point split endpoint 4096 114+point split endpoint 4096 115)/2)
    have hp : upperPayment 114 = (417988436014:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 114+point split endpoint 4096 115)/2 = (579031227:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579031227:ℝ)/168755200)*ClassicalSixthBranch.v ((579031227:ℝ)/168755200)/ClassicalSixthBranch.r = (160002121690281:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_114
  · change upperPayment 115 ≤ upperValue ((point split endpoint 4096 115+point split endpoint 4096 116)/2)
    have hp : upperPayment 115 = (417932143786:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 115+point split endpoint 4096 116)/2 = (579056377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579056377:ℝ)/168755200)*ClassicalSixthBranch.v ((579056377:ℝ)/168755200)/ClassicalSixthBranch.r = (159976337141697:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_115
  · change upperPayment 116 ≤ upperValue ((point split endpoint 4096 116+point split endpoint 4096 117)/2)
    have hp : upperPayment 116 = (417875832061:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 116+point split endpoint 4096 117)/2 = (579081527:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579081527:ℝ)/168755200)*ClassicalSixthBranch.v ((579081527:ℝ)/168755200)/ClassicalSixthBranch.r = (159950554617185:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_116
  · change upperPayment 117 ≤ upperValue ((point split endpoint 4096 117+point split endpoint 4096 118)/2)
    have hp : upperPayment 117 = (417819500837:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 117+point split endpoint 4096 118)/2 = (579106677:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579106677:ℝ)/168755200)*ClassicalSixthBranch.v ((579106677:ℝ)/168755200)/ClassicalSixthBranch.r = (159924774116745:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_117
  · change upperPayment 118 ≤ upperValue ((point split endpoint 4096 118+point split endpoint 4096 119)/2)
    have hp : upperPayment 118 = (417763150112:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 118+point split endpoint 4096 119)/2 = (579131827:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579131827:ℝ)/168755200)*ClassicalSixthBranch.v ((579131827:ℝ)/168755200)/ClassicalSixthBranch.r = (159898995640377:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_118
  · change upperPayment 119 ≤ upperValue ((point split endpoint 4096 119+point split endpoint 4096 120)/2)
    have hp : upperPayment 119 = (417706779884:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 119+point split endpoint 4096 120)/2 = (579156977:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579156977:ℝ)/168755200)*ClassicalSixthBranch.v ((579156977:ℝ)/168755200)/ClassicalSixthBranch.r = (159873219188081:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_119
  · change upperPayment 120 ≤ upperValue ((point split endpoint 4096 120+point split endpoint 4096 121)/2)
    have hp : upperPayment 120 = (417650390150:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 120+point split endpoint 4096 121)/2 = (579182127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579182127:ℝ)/168755200)*ClassicalSixthBranch.v ((579182127:ℝ)/168755200)/ClassicalSixthBranch.r = (159847444759857:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_120
  · change upperPayment 121 ≤ upperValue ((point split endpoint 4096 121+point split endpoint 4096 122)/2)
    have hp : upperPayment 121 = (417593980909:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 121+point split endpoint 4096 122)/2 = (579207277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579207277:ℝ)/168755200)*ClassicalSixthBranch.v ((579207277:ℝ)/168755200)/ClassicalSixthBranch.r = (159821672355705:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_121
  · change upperPayment 122 ≤ upperValue ((point split endpoint 4096 122+point split endpoint 4096 123)/2)
    have hp : upperPayment 122 = (417537552157:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 122+point split endpoint 4096 123)/2 = (579232427:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579232427:ℝ)/168755200)*ClassicalSixthBranch.v ((579232427:ℝ)/168755200)/ClassicalSixthBranch.r = (159795901975625:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_122
  · change upperPayment 123 ≤ upperValue ((point split endpoint 4096 123+point split endpoint 4096 124)/2)
    have hp : upperPayment 123 = (417481103894:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 123+point split endpoint 4096 124)/2 = (579257577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579257577:ℝ)/168755200)*ClassicalSixthBranch.v ((579257577:ℝ)/168755200)/ClassicalSixthBranch.r = (159770133619617:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_123
  · change upperPayment 124 ≤ upperValue ((point split endpoint 4096 124+point split endpoint 4096 125)/2)
    have hp : upperPayment 124 = (417424636115:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 124+point split endpoint 4096 125)/2 = (579282727:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579282727:ℝ)/168755200)*ClassicalSixthBranch.v ((579282727:ℝ)/168755200)/ClassicalSixthBranch.r = (159744367287681:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_124
  · change upperPayment 125 ≤ upperValue ((point split endpoint 4096 125+point split endpoint 4096 126)/2)
    have hp : upperPayment 125 = (417368148820:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 125+point split endpoint 4096 126)/2 = (579307877:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579307877:ℝ)/168755200)*ClassicalSixthBranch.v ((579307877:ℝ)/168755200)/ClassicalSixthBranch.r = (159718602979817:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_125
  · change upperPayment 126 ≤ upperValue ((point split endpoint 4096 126+point split endpoint 4096 127)/2)
    have hp : upperPayment 126 = (417311642006:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 126+point split endpoint 4096 127)/2 = (579333027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579333027:ℝ)/168755200)*ClassicalSixthBranch.v ((579333027:ℝ)/168755200)/ClassicalSixthBranch.r = (159692840696025:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_126
  · change upperPayment 127 ≤ upperValue ((point split endpoint 4096 127+point split endpoint 4096 128)/2)
    have hp : upperPayment 127 = (417255115670:ℝ)/1000000000000 := rfl
    have hx : (point split endpoint 4096 127+point split endpoint 4096 128)/2 = (579358177:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.u ((579358177:ℝ)/168755200)*ClassicalSixthBranch.v ((579358177:ℝ)/168755200)/ClassicalSixthBranch.r = (159667080436305:ℝ)/73380053123072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold upperValue
    rw [hr]
    exact paid_upper_127
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.upper_grid_block_007
