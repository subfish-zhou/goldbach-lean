import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints255
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_255 (j : Fin 16) : lowerPayment (16*255+j.val) ≤
    lowerValue ((point 2 split 4096 (16*255+j.val)+point 2 split 4096 (16*255+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 4080 ≤ lowerValue ((point 2 split 4096 4080+point 2 split 4096 4081)/2)
    have hp : lowerPayment 4080 = (422715442017:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4080+point 2 split 4096 4081)/2 = (575248491:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575248491:ℝ)/168755200)/ClassicalSixthBranch.v ((575248491:ℝ)/168755200) = (498536729947:ℝ)/224682272664 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4080
  · change lowerPayment 4081 ≤ lowerValue ((point 2 split 4096 4081+point 2 split 4096 4082)/2)
    have hp : lowerPayment 4081 = (422817868545:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4081+point 2 split 4096 4082)/2 = (575306753:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575306753:ℝ)/168755200)/ClassicalSixthBranch.v ((575306753:ℝ)/168755200) = (498459416273:ℝ)/224634264776 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4081
  · change lowerPayment 4082 ≤ lowerValue ((point 2 split 4096 4082+point 2 split 4096 4083)/2)
    have hp : lowerPayment 4082 = (422920317144:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4082+point 2 split 4096 4083)/2 = (115073003:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((115073003:ℝ)/33751040)/ClassicalSixthBranch.v ((115073003:ℝ)/33751040) = (498382102599:ℝ)/224586256888 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4082
  · change lowerPayment 4083 ≤ lowerValue ((point 2 split 4096 4083+point 2 split 4096 4084)/2)
    have hp : lowerPayment 4083 = (423022787833:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4083+point 2 split 4096 4084)/2 = (575423277:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575423277:ℝ)/168755200)/ClassicalSixthBranch.v ((575423277:ℝ)/168755200) = (19932191557:ℝ)/8981529960 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4083
  · change lowerPayment 4084 ≤ lowerValue ((point 2 split 4096 4084+point 2 split 4096 4085)/2)
    have hp : lowerPayment 4084 = (423125280631:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4084+point 2 split 4096 4085)/2 = (575481539:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575481539:ℝ)/168755200)/ClassicalSixthBranch.v ((575481539:ℝ)/168755200) = (498227475251:ℝ)/224490241112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4084
  · change lowerPayment 4085 ≤ lowerValue ((point 2 split 4096 4085+point 2 split 4096 4086)/2)
    have hp : lowerPayment 4085 = (423227795559:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4085+point 2 split 4096 4086)/2 = (575539801:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575539801:ℝ)/168755200)/ClassicalSixthBranch.v ((575539801:ℝ)/168755200) = (498150161577:ℝ)/224442233224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4085
  · change lowerPayment 4086 ≤ lowerValue ((point 2 split 4096 4086+point 2 split 4096 4087)/2)
    have hp : lowerPayment 4086 = (423330332636:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4086+point 2 split 4096 4087)/2 = (575598063:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575598063:ℝ)/168755200)/ClassicalSixthBranch.v ((575598063:ℝ)/168755200) = (498072847903:ℝ)/224394225336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4086
  · change lowerPayment 4087 ≤ lowerValue ((point 2 split 4096 4087+point 2 split 4096 4088)/2)
    have hp : lowerPayment 4087 = (423432891882:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4087+point 2 split 4096 4088)/2 = (23026253:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((23026253:ℝ)/6750208)/ClassicalSixthBranch.v ((23026253:ℝ)/6750208) = (497995534229:ℝ)/224346217448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4087
  · change lowerPayment 4088 ≤ lowerValue ((point 2 split 4096 4088+point 2 split 4096 4089)/2)
    have hp : lowerPayment 4088 = (423535473317:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4088+point 2 split 4096 4089)/2 = (575714587:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575714587:ℝ)/168755200)/ClassicalSixthBranch.v ((575714587:ℝ)/168755200) = (99583644111:ℝ)/44859641912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4088
  · change lowerPayment 4089 ≤ lowerValue ((point 2 split 4096 4089+point 2 split 4096 4090)/2)
    have hp : lowerPayment 4089 = (423638076961:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4089+point 2 split 4096 4090)/2 = (575772849:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575772849:ℝ)/168755200)/ClassicalSixthBranch.v ((575772849:ℝ)/168755200) = (497840906881:ℝ)/224250201672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4089
  · change lowerPayment 4090 ≤ lowerValue ((point 2 split 4096 4090+point 2 split 4096 4091)/2)
    have hp : lowerPayment 4090 = (423740702833:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4090+point 2 split 4096 4091)/2 = (575831111:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575831111:ℝ)/168755200)/ClassicalSixthBranch.v ((575831111:ℝ)/168755200) = (497763593207:ℝ)/224202193784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4090
  · change lowerPayment 4091 ≤ lowerValue ((point 2 split 4096 4091+point 2 split 4096 4092)/2)
    have hp : lowerPayment 4091 = (423843350952:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4091+point 2 split 4096 4092)/2 = (575889373:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((575889373:ℝ)/168755200)/ClassicalSixthBranch.v ((575889373:ℝ)/168755200) = (497686279533:ℝ)/224154185896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4091
  · change lowerPayment 4092 ≤ lowerValue ((point 2 split 4096 4092+point 2 split 4096 4093)/2)
    have hp : lowerPayment 4092 = (423946021340:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4092+point 2 split 4096 4093)/2 = (115189527:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((115189527:ℝ)/33751040)/ClassicalSixthBranch.v ((115189527:ℝ)/33751040) = (497608965859:ℝ)/224106178008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4092
  · change lowerPayment 4093 ≤ lowerValue ((point 2 split 4096 4093+point 2 split 4096 4094)/2)
    have hp : lowerPayment 4093 = (424048714016:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4093+point 2 split 4096 4094)/2 = (576005897:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((576005897:ℝ)/168755200)/ClassicalSixthBranch.v ((576005897:ℝ)/168755200) = (99506330437:ℝ)/44811634024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4093
  · change lowerPayment 4094 ≤ lowerValue ((point 2 split 4096 4094+point 2 split 4096 4095)/2)
    have hp : lowerPayment 4094 = (424151428998:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4094+point 2 split 4096 4095)/2 = (576064159:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((576064159:ℝ)/168755200)/ClassicalSixthBranch.v ((576064159:ℝ)/168755200) = (497454338511:ℝ)/224010162232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4094
  · change lowerPayment 4095 ≤ lowerValue ((point 2 split 4096 4095+point 2 split 4096 4096)/2)
    have hp : lowerPayment 4095 = (424254166309:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 4095+point 2 split 4096 4096)/2 = (576122421:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((576122421:ℝ)/168755200)/ClassicalSixthBranch.v ((576122421:ℝ)/168755200) = (497377024837:ℝ)/223962154344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_4095
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_255
