import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints008
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_008 (j : Fin 16) : lowerPayment (16*8+j.val) ≤
    lowerValue ((point 2 split 4096 (16*8+j.val)+point 2 split 4096 (16*8+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 128 ≤ lowerValue ((point 2 split 4096 128+point 2 split 4096 129)/2)
    have hp : lowerPayment 128 = (20341967085:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 128+point 2 split 4096 129)/2 = (344997067:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((344997067:ℝ)/168755200)/ClassicalSixthBranch.v ((344997067:ℝ)/168755200) = (160816073919:ℝ)/82881889208 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_128
  · change lowerPayment 129 ≤ lowerValue ((point 2 split 4096 129+point 2 split 4096 130)/2)
    have hp : lowerPayment 129 = (20495547600:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 129+point 2 split 4096 130)/2 = (345055329:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345055329:ℝ)/168755200)/ClassicalSixthBranch.v ((345055329:ℝ)/168755200) = (804003055921:ℝ)/414361438152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_129
  · change lowerPayment 130 ≤ lowerValue ((point 2 split 4096 130+point 2 split 4096 131)/2)
    have hp : lowerPayment 130 = (20649058038:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 130+point 2 split 4096 131)/2 = (345113591:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345113591:ℝ)/168755200)/ClassicalSixthBranch.v ((345113591:ℝ)/168755200) = (803925742247:ℝ)/414313430264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_130
  · change lowerPayment 131 ≤ lowerValue ((point 2 split 4096 131+point 2 split 4096 132)/2)
    have hp : lowerPayment 131 = (20802498464:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 131+point 2 split 4096 132)/2 = (345171853:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345171853:ℝ)/168755200)/ClassicalSixthBranch.v ((345171853:ℝ)/168755200) = (803848428573:ℝ)/414265422376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_131
  · change lowerPayment 132 ≤ lowerValue ((point 2 split 4096 132+point 2 split 4096 133)/2)
    have hp : lowerPayment 132 = (20955868940:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 132+point 2 split 4096 133)/2 = (69046023:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69046023:ℝ)/33751040)/ClassicalSixthBranch.v ((69046023:ℝ)/33751040) = (803771114899:ℝ)/414217414488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_132
  · change lowerPayment 133 ≤ lowerValue ((point 2 split 4096 133+point 2 split 4096 134)/2)
    have hp : lowerPayment 133 = (21109169531:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 133+point 2 split 4096 134)/2 = (345288377:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345288377:ℝ)/168755200)/ClassicalSixthBranch.v ((345288377:ℝ)/168755200) = (32147752049:ℝ)/16566776264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_133
  · change lowerPayment 134 ≤ lowerValue ((point 2 split 4096 134+point 2 split 4096 135)/2)
    have hp : lowerPayment 134 = (21262400299:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 134+point 2 split 4096 135)/2 = (345346639:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345346639:ℝ)/168755200)/ClassicalSixthBranch.v ((345346639:ℝ)/168755200) = (803616487551:ℝ)/414121398712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_134
  · change lowerPayment 135 ≤ lowerValue ((point 2 split 4096 135+point 2 split 4096 136)/2)
    have hp : lowerPayment 135 = (21415561309:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 135+point 2 split 4096 136)/2 = (345404901:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345404901:ℝ)/168755200)/ClassicalSixthBranch.v ((345404901:ℝ)/168755200) = (803539173877:ℝ)/414073390824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_135
  · change lowerPayment 136 ≤ lowerValue ((point 2 split 4096 136+point 2 split 4096 137)/2)
    have hp : lowerPayment 136 = (21568652622:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 136+point 2 split 4096 137)/2 = (345463163:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345463163:ℝ)/168755200)/ClassicalSixthBranch.v ((345463163:ℝ)/168755200) = (803461860203:ℝ)/414025382936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_136
  · change lowerPayment 137 ≤ lowerValue ((point 2 split 4096 137+point 2 split 4096 138)/2)
    have hp : lowerPayment 137 = (21721674303:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 137+point 2 split 4096 138)/2 = (13820857:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((13820857:ℝ)/6750208)/ClassicalSixthBranch.v ((13820857:ℝ)/6750208) = (803384546529:ℝ)/413977375048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_137
  · change lowerPayment 138 ≤ lowerValue ((point 2 split 4096 138+point 2 split 4096 139)/2)
    have hp : lowerPayment 138 = (21874626415:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 138+point 2 split 4096 139)/2 = (345579687:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345579687:ℝ)/168755200)/ClassicalSixthBranch.v ((345579687:ℝ)/168755200) = (160661446571:ℝ)/82785873432 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_138
  · change lowerPayment 139 ≤ lowerValue ((point 2 split 4096 139+point 2 split 4096 140)/2)
    have hp : lowerPayment 139 = (22027509020:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 139+point 2 split 4096 140)/2 = (345637949:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345637949:ℝ)/168755200)/ClassicalSixthBranch.v ((345637949:ℝ)/168755200) = (803229919181:ℝ)/413881359272 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_139
  · change lowerPayment 140 ≤ lowerValue ((point 2 split 4096 140+point 2 split 4096 141)/2)
    have hp : lowerPayment 140 = (22180322181:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 140+point 2 split 4096 141)/2 = (345696211:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345696211:ℝ)/168755200)/ClassicalSixthBranch.v ((345696211:ℝ)/168755200) = (803152605507:ℝ)/413833351384 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_140
  · change lowerPayment 141 ≤ lowerValue ((point 2 split 4096 141+point 2 split 4096 142)/2)
    have hp : lowerPayment 141 = (22333065963:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 141+point 2 split 4096 142)/2 = (345754473:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345754473:ℝ)/168755200)/ClassicalSixthBranch.v ((345754473:ℝ)/168755200) = (803075291833:ℝ)/413785343496 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_141
  · change lowerPayment 142 ≤ lowerValue ((point 2 split 4096 142+point 2 split 4096 143)/2)
    have hp : lowerPayment 142 = (22485740427:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 142+point 2 split 4096 143)/2 = (69162547:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((69162547:ℝ)/33751040)/ClassicalSixthBranch.v ((69162547:ℝ)/33751040) = (802997978159:ℝ)/413737335608 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_142
  · change lowerPayment 143 ≤ lowerValue ((point 2 split 4096 143+point 2 split 4096 144)/2)
    have hp : lowerPayment 143 = (22638345636:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 143+point 2 split 4096 144)/2 = (345870997:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((345870997:ℝ)/168755200)/ClassicalSixthBranch.v ((345870997:ℝ)/168755200) = (160584132897:ℝ)/82737865544 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_143
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_008
