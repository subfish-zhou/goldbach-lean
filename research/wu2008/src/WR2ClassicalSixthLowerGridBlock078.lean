import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints078
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_078 (j : Fin 16) : lowerPayment (16*78+j.val) ≤
    lowerValue ((point 2 split 4096 (16*78+j.val)+point 2 split 4096 (16*78+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 1248 ≤ lowerValue ((point 2 split 4096 1248+point 2 split 4096 1249)/2)
    have hp : lowerPayment 1248 = (160055058279:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1248+point 2 split 4096 1249)/2 = (410250507:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410250507:ℝ)/168755200)/ClassicalSixthBranch.v ((410250507:ℝ)/168755200) = (143497810943:ℝ)/72128122296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1248
  · change lowerPayment 1249 ≤ lowerValue ((point 2 split 4096 1249+point 2 split 4096 1250)/2)
    have hp : lowerPayment 1249 = (160159100978:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1249+point 2 split 4096 1250)/2 = (410308769:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410308769:ℝ)/168755200)/ClassicalSixthBranch.v ((410308769:ℝ)/168755200) = (717411741041:ℝ)/360592603592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1249
  · change lowerPayment 1250 ≤ lowerValue ((point 2 split 4096 1250+point 2 split 4096 1251)/2)
    have hp : lowerPayment 1250 = (160263118345:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1250+point 2 split 4096 1251)/2 = (410367031:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410367031:ℝ)/168755200)/ClassicalSixthBranch.v ((410367031:ℝ)/168755200) = (717334427367:ℝ)/360544595704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1250
  · change lowerPayment 1251 ≤ lowerValue ((point 2 split 4096 1251+point 2 split 4096 1252)/2)
    have hp : lowerPayment 1251 = (160367110404:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1251+point 2 split 4096 1252)/2 = (410425293:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410425293:ℝ)/168755200)/ClassicalSixthBranch.v ((410425293:ℝ)/168755200) = (717257113693:ℝ)/360496587816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1251
  · change lowerPayment 1252 ≤ lowerValue ((point 2 split 4096 1252+point 2 split 4096 1253)/2)
    have hp : lowerPayment 1252 = (160471077181:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1252+point 2 split 4096 1253)/2 = (82096711:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82096711:ℝ)/33751040)/ClassicalSixthBranch.v ((82096711:ℝ)/33751040) = (717179800019:ℝ)/360448579928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1252
  · change lowerPayment 1253 ≤ lowerValue ((point 2 split 4096 1253+point 2 split 4096 1254)/2)
    have hp : lowerPayment 1253 = (160575018700:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1253+point 2 split 4096 1254)/2 = (410541817:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410541817:ℝ)/168755200)/ClassicalSixthBranch.v ((410541817:ℝ)/168755200) = (143420497269:ℝ)/72080114408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1253
  · change lowerPayment 1254 ≤ lowerValue ((point 2 split 4096 1254+point 2 split 4096 1255)/2)
    have hp : lowerPayment 1254 = (160678934986:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1254+point 2 split 4096 1255)/2 = (410600079:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410600079:ℝ)/168755200)/ClassicalSixthBranch.v ((410600079:ℝ)/168755200) = (717025172671:ℝ)/360352564152 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1254
  · change lowerPayment 1255 ≤ lowerValue ((point 2 split 4096 1255+point 2 split 4096 1256)/2)
    have hp : lowerPayment 1255 = (160782826064:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1255+point 2 split 4096 1256)/2 = (410658341:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410658341:ℝ)/168755200)/ClassicalSixthBranch.v ((410658341:ℝ)/168755200) = (716947858997:ℝ)/360304556264 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1255
  · change lowerPayment 1256 ≤ lowerValue ((point 2 split 4096 1256+point 2 split 4096 1257)/2)
    have hp : lowerPayment 1256 = (160886691958:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1256+point 2 split 4096 1257)/2 = (410716603:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410716603:ℝ)/168755200)/ClassicalSixthBranch.v ((410716603:ℝ)/168755200) = (716870545323:ℝ)/360256548376 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1256
  · change lowerPayment 1257 ≤ lowerValue ((point 2 split 4096 1257+point 2 split 4096 1258)/2)
    have hp : lowerPayment 1257 = (160990532694:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1257+point 2 split 4096 1258)/2 = (82154973:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((82154973:ℝ)/33751040)/ClassicalSixthBranch.v ((82154973:ℝ)/33751040) = (716793231649:ℝ)/360208540488 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1257
  · change lowerPayment 1258 ≤ lowerValue ((point 2 split 4096 1258+point 2 split 4096 1259)/2)
    have hp : lowerPayment 1258 = (161094348297:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1258+point 2 split 4096 1259)/2 = (410833127:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410833127:ℝ)/168755200)/ClassicalSixthBranch.v ((410833127:ℝ)/168755200) = (28668636719:ℝ)/14406421304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1258
  · change lowerPayment 1259 ≤ lowerValue ((point 2 split 4096 1259+point 2 split 4096 1260)/2)
    have hp : lowerPayment 1259 = (161198138790:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1259+point 2 split 4096 1260)/2 = (410891389:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410891389:ℝ)/168755200)/ClassicalSixthBranch.v ((410891389:ℝ)/168755200) = (716638604301:ℝ)/360112524712 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1259
  · change lowerPayment 1260 ≤ lowerValue ((point 2 split 4096 1260+point 2 split 4096 1261)/2)
    have hp : lowerPayment 1260 = (161301904198:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1260+point 2 split 4096 1261)/2 = (410949651:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((410949651:ℝ)/168755200)/ClassicalSixthBranch.v ((410949651:ℝ)/168755200) = (716561290627:ℝ)/360064516824 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1260
  · change lowerPayment 1261 ≤ lowerValue ((point 2 split 4096 1261+point 2 split 4096 1262)/2)
    have hp : lowerPayment 1261 = (161405644547:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1261+point 2 split 4096 1262)/2 = (411007913:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411007913:ℝ)/168755200)/ClassicalSixthBranch.v ((411007913:ℝ)/168755200) = (716483976953:ℝ)/360016508936 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1261
  · change lowerPayment 1262 ≤ lowerValue ((point 2 split 4096 1262+point 2 split 4096 1263)/2)
    have hp : lowerPayment 1262 = (161509359862:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1262+point 2 split 4096 1263)/2 = (16442647:ℝ)/6750208 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((16442647:ℝ)/6750208)/ClassicalSixthBranch.v ((16442647:ℝ)/6750208) = (716406663279:ℝ)/359968501048 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1262
  · change lowerPayment 1263 ≤ lowerValue ((point 2 split 4096 1263+point 2 split 4096 1264)/2)
    have hp : lowerPayment 1263 = (161613050165:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 1263+point 2 split 4096 1264)/2 = (411124437:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((411124437:ℝ)/168755200)/ClassicalSixthBranch.v ((411124437:ℝ)/168755200) = (143265869921:ℝ)/71984098632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_1263
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_078
