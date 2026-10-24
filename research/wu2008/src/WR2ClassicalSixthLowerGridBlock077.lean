import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints077
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_077 (j : Fin 16) : lowerPayment (16*77+j.val) ≤
    lowerValue ((point 2 split 4096 (16*77+j.val)+point 2 split 4096 (16*77+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1232 ≤ lowerValue ((point 2 split 4096 1232+point 2 split 4096 1233)/2)
    have hp : lowerPayment 1232 = (158386909549:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1232+point 2 split 4096 1233)/2 = (81863663:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81863663:ℝ)/33751040)/ClassicalSixthBranch.v ((81863663:ℝ)/33751040) = (718726073499:ℝ)/361408737688 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1232
  · change lowerPayment 1233 ≤ lowerValue ((point 2 split 4096 1233+point 2 split 4096 1234)/2)
    have hp : lowerPayment 1233 = (158491360960:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1233+point 2 split 4096 1234)/2 = (409376577:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409376577:ℝ)/168755200)/ClassicalSixthBranch.v ((409376577:ℝ)/168755200) = (28745950393:ℝ)/14454429192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1233
  · change lowerPayment 1234 ≤ lowerValue ((point 2 split 4096 1234+point 2 split 4096 1235)/2)
    have hp : lowerPayment 1234 = (158595786638:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1234+point 2 split 4096 1235)/2 = (409434839:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409434839:ℝ)/168755200)/ClassicalSixthBranch.v ((409434839:ℝ)/168755200) = (718571446151:ℝ)/361312721912 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1234
  · change lowerPayment 1235 ≤ lowerValue ((point 2 split 4096 1235+point 2 split 4096 1236)/2)
    have hp : lowerPayment 1235 = (158700186609:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1235+point 2 split 4096 1236)/2 = (409493101:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409493101:ℝ)/168755200)/ClassicalSixthBranch.v ((409493101:ℝ)/168755200) = (718494132477:ℝ)/361264714024 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1235
  · change lowerPayment 1236 ≤ lowerValue ((point 2 split 4096 1236+point 2 split 4096 1237)/2)
    have hp : lowerPayment 1236 = (158804560898:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1236+point 2 split 4096 1237)/2 = (409551363:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409551363:ℝ)/168755200)/ClassicalSixthBranch.v ((409551363:ℝ)/168755200) = (718416818803:ℝ)/361216706136 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1236
  · change lowerPayment 1237 ≤ lowerValue ((point 2 split 4096 1237+point 2 split 4096 1238)/2)
    have hp : lowerPayment 1237 = (158908909530:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1237+point 2 split 4096 1238)/2 = (16384385:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16384385:ℝ)/6750208)/ClassicalSixthBranch.v ((16384385:ℝ)/6750208) = (718339505129:ℝ)/361168698248 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1237
  · change lowerPayment 1238 ≤ lowerValue ((point 2 split 4096 1238+point 2 split 4096 1239)/2)
    have hp : lowerPayment 1238 = (159013232530:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1238+point 2 split 4096 1239)/2 = (409667887:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409667887:ℝ)/168755200)/ClassicalSixthBranch.v ((409667887:ℝ)/168755200) = (143652438291:ℝ)/72224138072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1238
  · change lowerPayment 1239 ≤ lowerValue ((point 2 split 4096 1239+point 2 split 4096 1240)/2)
    have hp : lowerPayment 1239 = (159117529924:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1239+point 2 split 4096 1240)/2 = (409726149:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409726149:ℝ)/168755200)/ClassicalSixthBranch.v ((409726149:ℝ)/168755200) = (718184877781:ℝ)/361072682472 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1239
  · change lowerPayment 1240 ≤ lowerValue ((point 2 split 4096 1240+point 2 split 4096 1241)/2)
    have hp : lowerPayment 1240 = (159221801735:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1240+point 2 split 4096 1241)/2 = (409784411:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409784411:ℝ)/168755200)/ClassicalSixthBranch.v ((409784411:ℝ)/168755200) = (718107564107:ℝ)/361024674584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1240
  · change lowerPayment 1241 ≤ lowerValue ((point 2 split 4096 1241+point 2 split 4096 1242)/2)
    have hp : lowerPayment 1241 = (159326047989:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1241+point 2 split 4096 1242)/2 = (409842673:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409842673:ℝ)/168755200)/ClassicalSixthBranch.v ((409842673:ℝ)/168755200) = (718030250433:ℝ)/360976666696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1241
  · change lowerPayment 1242 ≤ lowerValue ((point 2 split 4096 1242+point 2 split 4096 1243)/2)
    have hp : lowerPayment 1242 = (159430268712:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1242+point 2 split 4096 1243)/2 = (81980187:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((81980187:ℝ)/33751040)/ClassicalSixthBranch.v ((81980187:ℝ)/33751040) = (717952936759:ℝ)/360928658808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1242
  · change lowerPayment 1243 ≤ lowerValue ((point 2 split 4096 1243+point 2 split 4096 1244)/2)
    have hp : lowerPayment 1243 = (159534463928:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1243+point 2 split 4096 1244)/2 = (409959197:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((409959197:ℝ)/168755200)/ClassicalSixthBranch.v ((409959197:ℝ)/168755200) = (143575124617:ℝ)/72176130184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1243
  · change lowerPayment 1244 ≤ lowerValue ((point 2 split 4096 1244+point 2 split 4096 1245)/2)
    have hp : lowerPayment 1244 = (159638633662:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1244+point 2 split 4096 1245)/2 = (410017459:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410017459:ℝ)/168755200)/ClassicalSixthBranch.v ((410017459:ℝ)/168755200) = (717798309411:ℝ)/360832643032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1244
  · change lowerPayment 1245 ≤ lowerValue ((point 2 split 4096 1245+point 2 split 4096 1246)/2)
    have hp : lowerPayment 1245 = (159742777939:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1245+point 2 split 4096 1246)/2 = (410075721:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410075721:ℝ)/168755200)/ClassicalSixthBranch.v ((410075721:ℝ)/168755200) = (717720995737:ℝ)/360784635144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1245
  · change lowerPayment 1246 ≤ lowerValue ((point 2 split 4096 1246+point 2 split 4096 1247)/2)
    have hp : lowerPayment 1246 = (159846896784:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1246+point 2 split 4096 1247)/2 = (410133983:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410133983:ℝ)/168755200)/ClassicalSixthBranch.v ((410133983:ℝ)/168755200) = (717643682063:ℝ)/360736627256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1246
  · change lowerPayment 1247 ≤ lowerValue ((point 2 split 4096 1247+point 2 split 4096 1248)/2)
    have hp : lowerPayment 1247 = (159950990223:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1247+point 2 split 4096 1248)/2 = (82038449:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82038449:ℝ)/33751040)/ClassicalSixthBranch.v ((82038449:ℝ)/33751040) = (717566368389:ℝ)/360688619368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1247
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_077
