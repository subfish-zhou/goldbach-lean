import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints140
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_140 (j : Fin 16) : lowerPayment (16*140+j.val) ≤
    lowerValue ((point 2 split 4096 (16*140+j.val)+point 2 split 4096 (16*140+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2240 ≤ lowerValue ((point 2 split 4096 2240+point 2 split 4096 2241)/2)
    have hp : lowerPayment 2240 = (254315318897:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2240+point 2 split 4096 2241)/2 = (468046411:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468046411:ℝ)/168755200)/ClassicalSixthBranch.v ((468046411:ℝ)/168755200) = (640793890107:ℝ)/313016786584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2240
  · change lowerPayment 2241 ≤ lowerValue ((point 2 split 4096 2241+point 2 split 4096 2242)/2)
    have hp : lowerPayment 2241 = (254404414479:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2241+point 2 split 4096 2242)/2 = (468104673:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468104673:ℝ)/168755200)/ClassicalSixthBranch.v ((468104673:ℝ)/168755200) = (640716576433:ℝ)/312968778696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2241
  · change lowerPayment 2242 ≤ lowerValue ((point 2 split 4096 2242+point 2 split 4096 2243)/2)
    have hp : lowerPayment 2242 = (254493503742:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2242+point 2 split 4096 2243)/2 = (93632587:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93632587:ℝ)/33751040)/ClassicalSixthBranch.v ((93632587:ℝ)/33751040) = (640639262759:ℝ)/312920770808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2242
  · change lowerPayment 2243 ≤ lowerValue ((point 2 split 4096 2243+point 2 split 4096 2244)/2)
    have hp : lowerPayment 2243 = (254582586700:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2243+point 2 split 4096 2244)/2 = (468221197:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468221197:ℝ)/168755200)/ClassicalSixthBranch.v ((468221197:ℝ)/168755200) = (128112389817:ℝ)/62574552584 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2243
  · change lowerPayment 2244 ≤ lowerValue ((point 2 split 4096 2244+point 2 split 4096 2245)/2)
    have hp : lowerPayment 2244 = (254671663371:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2244+point 2 split 4096 2245)/2 = (468279459:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468279459:ℝ)/168755200)/ClassicalSixthBranch.v ((468279459:ℝ)/168755200) = (640484635411:ℝ)/312824755032 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2244
  · change lowerPayment 2245 ≤ lowerValue ((point 2 split 4096 2245+point 2 split 4096 2246)/2)
    have hp : lowerPayment 2245 = (254760733768:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2245+point 2 split 4096 2246)/2 = (468337721:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468337721:ℝ)/168755200)/ClassicalSixthBranch.v ((468337721:ℝ)/168755200) = (640407321737:ℝ)/312776747144 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2245
  · change lowerPayment 2246 ≤ lowerValue ((point 2 split 4096 2246+point 2 split 4096 2247)/2)
    have hp : lowerPayment 2246 = (254849797908:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2246+point 2 split 4096 2247)/2 = (468395983:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468395983:ℝ)/168755200)/ClassicalSixthBranch.v ((468395983:ℝ)/168755200) = (640330008063:ℝ)/312728739256 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2246
  · change lowerPayment 2247 ≤ lowerValue ((point 2 split 4096 2247+point 2 split 4096 2248)/2)
    have hp : lowerPayment 2247 = (254938855806:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2247+point 2 split 4096 2248)/2 = (93690849:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93690849:ℝ)/33751040)/ClassicalSixthBranch.v ((93690849:ℝ)/33751040) = (640252694389:ℝ)/312680731368 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2247
  · change lowerPayment 2248 ≤ lowerValue ((point 2 split 4096 2248+point 2 split 4096 2249)/2)
    have hp : lowerPayment 2248 = (255027907477:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2248+point 2 split 4096 2249)/2 = (468512507:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468512507:ℝ)/168755200)/ClassicalSixthBranch.v ((468512507:ℝ)/168755200) = (128035076143:ℝ)/62526544696 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2248
  · change lowerPayment 2249 ≤ lowerValue ((point 2 split 4096 2249+point 2 split 4096 2250)/2)
    have hp : lowerPayment 2249 = (255116952936:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2249+point 2 split 4096 2250)/2 = (468570769:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468570769:ℝ)/168755200)/ClassicalSixthBranch.v ((468570769:ℝ)/168755200) = (640098067041:ℝ)/312584715592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2249
  · change lowerPayment 2250 ≤ lowerValue ((point 2 split 4096 2250+point 2 split 4096 2251)/2)
    have hp : lowerPayment 2250 = (255205992200:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2250+point 2 split 4096 2251)/2 = (468629031:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468629031:ℝ)/168755200)/ClassicalSixthBranch.v ((468629031:ℝ)/168755200) = (640020753367:ℝ)/312536707704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2250
  · change lowerPayment 2251 ≤ lowerValue ((point 2 split 4096 2251+point 2 split 4096 2252)/2)
    have hp : lowerPayment 2251 = (255295025283:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2251+point 2 split 4096 2252)/2 = (468687293:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468687293:ℝ)/168755200)/ClassicalSixthBranch.v ((468687293:ℝ)/168755200) = (639943439693:ℝ)/312488699816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2251
  · change lowerPayment 2252 ≤ lowerValue ((point 2 split 4096 2252+point 2 split 4096 2253)/2)
    have hp : lowerPayment 2252 = (255384052200:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2252+point 2 split 4096 2253)/2 = (93749111:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((93749111:ℝ)/33751040)/ClassicalSixthBranch.v ((93749111:ℝ)/33751040) = (639866126019:ℝ)/312440691928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2252
  · change lowerPayment 2253 ≤ lowerValue ((point 2 split 4096 2253+point 2 split 4096 2254)/2)
    have hp : lowerPayment 2253 = (255473072968:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2253+point 2 split 4096 2254)/2 = (468803817:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468803817:ℝ)/168755200)/ClassicalSixthBranch.v ((468803817:ℝ)/168755200) = (127957762469:ℝ)/62478536808 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2253
  · change lowerPayment 2254 ≤ lowerValue ((point 2 split 4096 2254+point 2 split 4096 2255)/2)
    have hp : lowerPayment 2254 = (255562087601:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2254+point 2 split 4096 2255)/2 = (468862079:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468862079:ℝ)/168755200)/ClassicalSixthBranch.v ((468862079:ℝ)/168755200) = (639711498671:ℝ)/312344676152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2254
  · change lowerPayment 2255 ≤ lowerValue ((point 2 split 4096 2255+point 2 split 4096 2256)/2)
    have hp : lowerPayment 2255 = (255651096115:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2255+point 2 split 4096 2256)/2 = (468920341:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((468920341:ℝ)/168755200)/ClassicalSixthBranch.v ((468920341:ℝ)/168755200) = (639634184997:ℝ)/312296668264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2255
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_140
