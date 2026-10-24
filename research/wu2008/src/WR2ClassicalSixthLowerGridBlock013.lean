import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints013
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_013 (j : Fin 16) : lowerPayment (16*13+j.val) ≤
    lowerValue ((point 2 split 4096 (16*13+j.val)+point 2 split 4096 (16*13+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 208 ≤ lowerValue ((point 2 split 4096 208+point 2 split 4096 209)/2)
    have hp : lowerPayment 208 = (32412090942:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 208+point 2 split 4096 209)/2 = (349658027:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349658027:ℝ)/168755200)/ClassicalSixthBranch.v ((349658027:ℝ)/168755200) = (31915811027:ℝ)/16422752600 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_208
  · change lowerPayment 209 ≤ lowerValue ((point 2 split 4096 209+point 2 split 4096 210)/2)
    have hp : lowerPayment 209 = (32560261099:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 209+point 2 split 4096 210)/2 = (349716289:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349716289:ℝ)/168755200)/ClassicalSixthBranch.v ((349716289:ℝ)/168755200) = (797817962001:ℝ)/410520807112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_209
  · change lowerPayment 210 ≤ lowerValue ((point 2 split 4096 210+point 2 split 4096 211)/2)
    have hp : lowerPayment 210 = (32708366069:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 210+point 2 split 4096 211)/2 = (349774551:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349774551:ℝ)/168755200)/ClassicalSixthBranch.v ((349774551:ℝ)/168755200) = (797740648327:ℝ)/410472799224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_210
  · change lowerPayment 211 ≤ lowerValue ((point 2 split 4096 211+point 2 split 4096 212)/2)
    have hp : lowerPayment 211 = (32856405911:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 211+point 2 split 4096 212)/2 = (349832813:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349832813:ℝ)/168755200)/ClassicalSixthBranch.v ((349832813:ℝ)/168755200) = (797663334653:ℝ)/410424791336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_211
  · change lowerPayment 212 ≤ lowerValue ((point 2 split 4096 212+point 2 split 4096 213)/2)
    have hp : lowerPayment 212 = (33004380683:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 212+point 2 split 4096 213)/2 = (13995643:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((13995643:ℝ)/6750208)/ClassicalSixthBranch.v ((13995643:ℝ)/6750208) = (797586020979:ℝ)/410376783448 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_212
  · change lowerPayment 213 ≤ lowerValue ((point 2 split 4096 213+point 2 split 4096 214)/2)
    have hp : lowerPayment 213 = (33152290445:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 213+point 2 split 4096 214)/2 = (349949337:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((349949337:ℝ)/168755200)/ClassicalSixthBranch.v ((349949337:ℝ)/168755200) = (159501741461:ℝ)/82065755112 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_213
  · change lowerPayment 214 ≤ lowerValue ((point 2 split 4096 214+point 2 split 4096 215)/2)
    have hp : lowerPayment 214 = (33300135253:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 214+point 2 split 4096 215)/2 = (350007599:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350007599:ℝ)/168755200)/ClassicalSixthBranch.v ((350007599:ℝ)/168755200) = (797431393631:ℝ)/410280767672 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_214
  · change lowerPayment 215 ≤ lowerValue ((point 2 split 4096 215+point 2 split 4096 216)/2)
    have hp : lowerPayment 215 = (33447915168:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 215+point 2 split 4096 216)/2 = (350065861:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350065861:ℝ)/168755200)/ClassicalSixthBranch.v ((350065861:ℝ)/168755200) = (797354079957:ℝ)/410232759784 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_215
  · change lowerPayment 216 ≤ lowerValue ((point 2 split 4096 216+point 2 split 4096 217)/2)
    have hp : lowerPayment 216 = (33595630247:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 216+point 2 split 4096 217)/2 = (350124123:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350124123:ℝ)/168755200)/ClassicalSixthBranch.v ((350124123:ℝ)/168755200) = (797276766283:ℝ)/410184751896 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_216
  · change lowerPayment 217 ≤ lowerValue ((point 2 split 4096 217+point 2 split 4096 218)/2)
    have hp : lowerPayment 217 = (33743280549:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 217+point 2 split 4096 218)/2 = (70036477:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70036477:ℝ)/33751040)/ClassicalSixthBranch.v ((70036477:ℝ)/33751040) = (797199452609:ℝ)/410136744008 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_217
  · change lowerPayment 218 ≤ lowerValue ((point 2 split 4096 218+point 2 split 4096 219)/2)
    have hp : lowerPayment 218 = (33890866131:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 218+point 2 split 4096 219)/2 = (350240647:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350240647:ℝ)/168755200)/ClassicalSixthBranch.v ((350240647:ℝ)/168755200) = (159424427787:ℝ)/82017747224 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_218
  · change lowerPayment 219 ≤ lowerValue ((point 2 split 4096 219+point 2 split 4096 220)/2)
    have hp : lowerPayment 219 = (34038387052:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 219+point 2 split 4096 220)/2 = (350298909:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350298909:ℝ)/168755200)/ClassicalSixthBranch.v ((350298909:ℝ)/168755200) = (797044825261:ℝ)/410040728232 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_219
  · change lowerPayment 220 ≤ lowerValue ((point 2 split 4096 220+point 2 split 4096 221)/2)
    have hp : lowerPayment 220 = (34185843371:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 220+point 2 split 4096 221)/2 = (350357171:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350357171:ℝ)/168755200)/ClassicalSixthBranch.v ((350357171:ℝ)/168755200) = (796967511587:ℝ)/409992720344 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_220
  · change lowerPayment 221 ≤ lowerValue ((point 2 split 4096 221+point 2 split 4096 222)/2)
    have hp : lowerPayment 221 = (34333235145:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 221+point 2 split 4096 222)/2 = (350415433:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350415433:ℝ)/168755200)/ClassicalSixthBranch.v ((350415433:ℝ)/168755200) = (796890197913:ℝ)/409944712456 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_221
  · change lowerPayment 222 ≤ lowerValue ((point 2 split 4096 222+point 2 split 4096 223)/2)
    have hp : lowerPayment 222 = (34480562433:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 222+point 2 split 4096 223)/2 = (70094739:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((70094739:ℝ)/33751040)/ClassicalSixthBranch.v ((70094739:ℝ)/33751040) = (796812884239:ℝ)/409896704568 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_222
  · change lowerPayment 223 ≤ lowerValue ((point 2 split 4096 223+point 2 split 4096 224)/2)
    have hp : lowerPayment 223 = (34627825292:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 223+point 2 split 4096 224)/2 = (350531957:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((350531957:ℝ)/168755200)/ClassicalSixthBranch.v ((350531957:ℝ)/168755200) = (159347114113:ℝ)/81969739336 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_223
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_013
