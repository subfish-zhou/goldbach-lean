import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints007
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_007 (j : Fin 16) : lowerPayment (16*7+j.val) ≤
    lowerValue ((point 2 split 4096 (16*7+j.val)+point 2 split 4096 (16*7+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 112 ≤ lowerValue ((point 2 split 4096 112+point 2 split 4096 113)/2)
    have hp : lowerPayment 112 = (17875096340:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 112+point 2 split 4096 113)/2 = (13762595:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((13762595:ℝ)/6750208)/ClassicalSixthBranch.v ((13762595:ℝ)/6750208) = (805317388379:ℝ)/415177572248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_112
  · change lowerPayment 113 ≤ lowerValue ((point 2 split 4096 113+point 2 split 4096 114)/2)
    have hp : lowerPayment 113 = (18029806776:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 113+point 2 split 4096 114)/2 = (344123137:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344123137:ℝ)/168755200)/ClassicalSixthBranch.v ((344123137:ℝ)/168755200) = (161048014941:ℝ)/83025912872 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_113
  · change lowerPayment 114 ≤ lowerValue ((point 2 split 4096 114+point 2 split 4096 115)/2)
    have hp : lowerPayment 114 = (18184446109:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 114+point 2 split 4096 115)/2 = (344181399:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344181399:ℝ)/168755200)/ClassicalSixthBranch.v ((344181399:ℝ)/168755200) = (805162761031:ℝ)/415081556472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_114
  · change lowerPayment 115 ≤ lowerValue ((point 2 split 4096 115+point 2 split 4096 116)/2)
    have hp : lowerPayment 115 = (18339014404:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 115+point 2 split 4096 116)/2 = (344239661:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344239661:ℝ)/168755200)/ClassicalSixthBranch.v ((344239661:ℝ)/168755200) = (805085447357:ℝ)/415033548584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_115
  · change lowerPayment 116 ≤ lowerValue ((point 2 split 4096 116+point 2 split 4096 117)/2)
    have hp : lowerPayment 116 = (18493511726:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 116+point 2 split 4096 117)/2 = (344297923:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344297923:ℝ)/168755200)/ClassicalSixthBranch.v ((344297923:ℝ)/168755200) = (805008133683:ℝ)/414985540696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_116
  · change lowerPayment 117 ≤ lowerValue ((point 2 split 4096 117+point 2 split 4096 118)/2)
    have hp : lowerPayment 117 = (18647938139:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 117+point 2 split 4096 118)/2 = (68871237:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68871237:ℝ)/33751040)/ClassicalSixthBranch.v ((68871237:ℝ)/33751040) = (804930820009:ℝ)/414937532808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_117
  · change lowerPayment 118 ≤ lowerValue ((point 2 split 4096 118+point 2 split 4096 119)/2)
    have hp : lowerPayment 118 = (18802293708:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 118+point 2 split 4096 119)/2 = (344414447:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344414447:ℝ)/168755200)/ClassicalSixthBranch.v ((344414447:ℝ)/168755200) = (160970701267:ℝ)/82977904984 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_118
  · change lowerPayment 119 ≤ lowerValue ((point 2 split 4096 119+point 2 split 4096 120)/2)
    have hp : lowerPayment 119 = (18956578497:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 119+point 2 split 4096 120)/2 = (344472709:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344472709:ℝ)/168755200)/ClassicalSixthBranch.v ((344472709:ℝ)/168755200) = (804776192661:ℝ)/414841517032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_119
  · change lowerPayment 120 ≤ lowerValue ((point 2 split 4096 120+point 2 split 4096 121)/2)
    have hp : lowerPayment 120 = (19110792570:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 120+point 2 split 4096 121)/2 = (344530971:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344530971:ℝ)/168755200)/ClassicalSixthBranch.v ((344530971:ℝ)/168755200) = (804698878987:ℝ)/414793509144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_120
  · change lowerPayment 121 ≤ lowerValue ((point 2 split 4096 121+point 2 split 4096 122)/2)
    have hp : lowerPayment 121 = (19264935992:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 121+point 2 split 4096 122)/2 = (344589233:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344589233:ℝ)/168755200)/ClassicalSixthBranch.v ((344589233:ℝ)/168755200) = (804621565313:ℝ)/414745501256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_121
  · change lowerPayment 122 ≤ lowerValue ((point 2 split 4096 122+point 2 split 4096 123)/2)
    have hp : lowerPayment 122 = (19419008826:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 122+point 2 split 4096 123)/2 = (68929499:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68929499:ℝ)/33751040)/ClassicalSixthBranch.v ((68929499:ℝ)/33751040) = (804544251639:ℝ)/414697493368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_122
  · change lowerPayment 123 ≤ lowerValue ((point 2 split 4096 123+point 2 split 4096 124)/2)
    have hp : lowerPayment 123 = (19573011138:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 123+point 2 split 4096 124)/2 = (344705757:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344705757:ℝ)/168755200)/ClassicalSixthBranch.v ((344705757:ℝ)/168755200) = (160893387593:ℝ)/82929897096 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_123
  · change lowerPayment 124 ≤ lowerValue ((point 2 split 4096 124+point 2 split 4096 125)/2)
    have hp : lowerPayment 124 = (19726942990:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 124+point 2 split 4096 125)/2 = (344764019:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344764019:ℝ)/168755200)/ClassicalSixthBranch.v ((344764019:ℝ)/168755200) = (804389624291:ℝ)/414601477592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_124
  · change lowerPayment 125 ≤ lowerValue ((point 2 split 4096 125+point 2 split 4096 126)/2)
    have hp : lowerPayment 125 = (19880804447:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 125+point 2 split 4096 126)/2 = (344822281:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344822281:ℝ)/168755200)/ClassicalSixthBranch.v ((344822281:ℝ)/168755200) = (804312310617:ℝ)/414553469704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_125
  · change lowerPayment 126 ≤ lowerValue ((point 2 split 4096 126+point 2 split 4096 127)/2)
    have hp : lowerPayment 126 = (20034595572:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 126+point 2 split 4096 127)/2 = (344880543:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344880543:ℝ)/168755200)/ClassicalSixthBranch.v ((344880543:ℝ)/168755200) = (804234996943:ℝ)/414505461816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_126
  · change lowerPayment 127 ≤ lowerValue ((point 2 split 4096 127+point 2 split 4096 128)/2)
    have hp : lowerPayment 127 = (20188316431:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 127+point 2 split 4096 128)/2 = (68987761:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((68987761:ℝ)/33751040)/ClassicalSixthBranch.v ((68987761:ℝ)/33751040) = (804157683269:ℝ)/414457453928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_127
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_007
