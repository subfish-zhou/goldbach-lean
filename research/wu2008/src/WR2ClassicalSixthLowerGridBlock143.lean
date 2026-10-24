import WR2ClassicalSixthLowerPayments
import WR2ClassicalSixthLowerPoints143
noncomputable section
namespace WuPaper.ClassicalSixthRational
open WuSource.SrcSixthGain ClassicalSixthQuadrature
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem lower_grid_block_143 (j : Fin 16) : lowerPayment (16*143+j.val) ≤
    lowerValue ((point 2 split 4096 (16*143+j.val)+point 2 split 4096 (16*143+j.val+1))/2) := by
  fin_cases j
  · change lowerPayment 2288 ≤ lowerValue ((point 2 split 4096 2288+point 2 split 4096 2289)/2)
    have hp : lowerPayment 2288 = (258585044503:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2288+point 2 split 4096 2289)/2 = (470842987:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470842987:ℝ)/168755200)/ClassicalSixthBranch.v ((470842987:ℝ)/168755200) = (127416566751:ℝ)/62142481592 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2288
  · change lowerPayment 2289 ≤ lowerValue ((point 2 split 4096 2289+point 2 split 4096 2290)/2)
    have hp : lowerPayment 2289 = (258673854075:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2289+point 2 split 4096 2290)/2 = (470901249:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470901249:ℝ)/168755200)/ClassicalSixthBranch.v ((470901249:ℝ)/168755200) = (637005520081:ℝ)/310664400072 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2289
  · change lowerPayment 2290 ≤ lowerValue ((point 2 split 4096 2290+point 2 split 4096 2291)/2)
    have hp : lowerPayment 2290 = (258762658062:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2290+point 2 split 4096 2291)/2 = (470959511:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((470959511:ℝ)/168755200)/ClassicalSixthBranch.v ((470959511:ℝ)/168755200) = (636928206407:ℝ)/310616392184 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2290
  · change lowerPayment 2291 ≤ lowerValue ((point 2 split 4096 2291+point 2 split 4096 2292)/2)
    have hp : lowerPayment 2291 = (258851456480:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2291+point 2 split 4096 2292)/2 = (471017773:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471017773:ℝ)/168755200)/ClassicalSixthBranch.v ((471017773:ℝ)/168755200) = (636850892733:ℝ)/310568384296 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2291
  · change lowerPayment 2292 ≤ lowerValue ((point 2 split 4096 2292+point 2 split 4096 2293)/2)
    have hp : lowerPayment 2292 = (258940249344:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2292+point 2 split 4096 2293)/2 = (94215207:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94215207:ℝ)/33751040)/ClassicalSixthBranch.v ((94215207:ℝ)/33751040) = (636773579059:ℝ)/310520376408 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2292
  · change lowerPayment 2293 ≤ lowerValue ((point 2 split 4096 2293+point 2 split 4096 2294)/2)
    have hp : lowerPayment 2293 = (259029036670:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2293+point 2 split 4096 2294)/2 = (471134297:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471134297:ℝ)/168755200)/ClassicalSixthBranch.v ((471134297:ℝ)/168755200) = (127339253077:ℝ)/62094473704 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2293
  · change lowerPayment 2294 ≤ lowerValue ((point 2 split 4096 2294+point 2 split 4096 2295)/2)
    have hp : lowerPayment 2294 = (259117818472:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2294+point 2 split 4096 2295)/2 = (471192559:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471192559:ℝ)/168755200)/ClassicalSixthBranch.v ((471192559:ℝ)/168755200) = (636618951711:ℝ)/310424360632 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2294
  · change lowerPayment 2295 ≤ lowerValue ((point 2 split 4096 2295+point 2 split 4096 2296)/2)
    have hp : lowerPayment 2295 = (259206594766:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2295+point 2 split 4096 2296)/2 = (471250821:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471250821:ℝ)/168755200)/ClassicalSixthBranch.v ((471250821:ℝ)/168755200) = (636541638037:ℝ)/310376352744 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2295
  · change lowerPayment 2296 ≤ lowerValue ((point 2 split 4096 2296+point 2 split 4096 2297)/2)
    have hp : lowerPayment 2296 = (259295365567:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2296+point 2 split 4096 2297)/2 = (471309083:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471309083:ℝ)/168755200)/ClassicalSixthBranch.v ((471309083:ℝ)/168755200) = (636464324363:ℝ)/310328344856 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2296
  · change lowerPayment 2297 ≤ lowerValue ((point 2 split 4096 2297+point 2 split 4096 2298)/2)
    have hp : lowerPayment 2297 = (259384130891:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2297+point 2 split 4096 2298)/2 = (94273469:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94273469:ℝ)/33751040)/ClassicalSixthBranch.v ((94273469:ℝ)/33751040) = (636387010689:ℝ)/310280336968 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2297
  · change lowerPayment 2298 ≤ lowerValue ((point 2 split 4096 2298+point 2 split 4096 2299)/2)
    have hp : lowerPayment 2298 = (259472890751:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2298+point 2 split 4096 2299)/2 = (471425607:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471425607:ℝ)/168755200)/ClassicalSixthBranch.v ((471425607:ℝ)/168755200) = (127261939403:ℝ)/62046465816 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2298
  · change lowerPayment 2299 ≤ lowerValue ((point 2 split 4096 2299+point 2 split 4096 2300)/2)
    have hp : lowerPayment 2299 = (259561645165:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2299+point 2 split 4096 2300)/2 = (471483869:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471483869:ℝ)/168755200)/ClassicalSixthBranch.v ((471483869:ℝ)/168755200) = (636232383341:ℝ)/310184321192 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2299
  · change lowerPayment 2300 ≤ lowerValue ((point 2 split 4096 2300+point 2 split 4096 2301)/2)
    have hp : lowerPayment 2300 = (259650394145:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2300+point 2 split 4096 2301)/2 = (471542131:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471542131:ℝ)/168755200)/ClassicalSixthBranch.v ((471542131:ℝ)/168755200) = (636155069667:ℝ)/310136313304 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2300
  · change lowerPayment 2301 ≤ lowerValue ((point 2 split 4096 2301+point 2 split 4096 2302)/2)
    have hp : lowerPayment 2301 = (259739137709:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2301+point 2 split 4096 2302)/2 = (471600393:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471600393:ℝ)/168755200)/ClassicalSixthBranch.v ((471600393:ℝ)/168755200) = (636077755993:ℝ)/310088305416 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2301
  · change lowerPayment 2302 ≤ lowerValue ((point 2 split 4096 2302+point 2 split 4096 2303)/2)
    have hp : lowerPayment 2302 = (259827875871:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2302+point 2 split 4096 2303)/2 = (94331731:ℝ)/33751040 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((94331731:ℝ)/33751040)/ClassicalSixthBranch.v ((94331731:ℝ)/33751040) = (636000442319:ℝ)/310040297528 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2302
  · change lowerPayment 2303 ≤ lowerValue ((point 2 split 4096 2303+point 2 split 4096 2304)/2)
    have hp : lowerPayment 2303 = (259916608646:ℝ)/1000000000000 := rfl
    have hx : (point 2 split 4096 2303+point 2 split 4096 2304)/2 = (471716917:ℝ)/168755200 := by
      norm_num [point,step,split,endpoint,QuarterTrim.alpha,QuarterTrim.beta]
    have hr : ClassicalSixthBranch.r*ClassicalSixthBranch.u ((471716917:ℝ)/168755200)/ClassicalSixthBranch.v ((471716917:ℝ)/168755200) = (127184625729:ℝ)/61998457928 := by
      norm_num [ClassicalSixthBranch.u,ClassicalSixthBranch.v,ClassicalSixthBranch.R,ClassicalSixthBranch.r]
    rw [hp,hx]
    unfold lowerValue
    rw [hr]
    exact paid_lower_2303
end WuPaper.ClassicalSixthRational
#print axioms WuPaper.ClassicalSixthRational.lower_grid_block_143
