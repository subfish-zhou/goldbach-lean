import F1ActualSecondConsumption

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1RemainingRecovery
open F1JointFTC
namespace F1ActualSecondFTC

/-- Normalize a quadratic logarithm by its existing repeated pole before paying logs. -/
theorem normalized_logs {am ap bm bp t : ℝ}
    (ham : 0 < am) (hap : 0 < ap) (hbm : 0 < bm) (hbp : 0 < bp) (ht : 0 < t) :
    log (am*ap/(bm*bp)) = 2*log t+log (am/(bm*t))-log (t*bp/ap) ∧
    log (am/bm)-log (ap/bp) = log (am/(bm*t))+log (t*bp/ap) := by
  rw [log_div (mul_ne_zero ham.ne' hap.ne') (mul_ne_zero hbm.ne' hbp.ne'),
    log_mul ham.ne' hap.ne',log_mul hbm.ne' hbp.ne',
    log_div ham.ne' (mul_ne_zero hbm.ne' ht.ne'),log_mul hbm.ne' ht.ne',
    log_div (mul_ne_zero ht.ne' hbp.ne') hap.ne',log_mul ht.ne' hbp.ne',
    log_div ham.ne' hbm.ne',log_div hap.ne' hbp.ne']
  constructor <;> ring

def refOne : ℝ := (927/200+2)/4
def refTwo : ℝ := (3*(927/200)-2)/4

def crossOneMinus : ℝ := (927/200+8-root)/((10-root)*refOne)
def crossOnePlus : ℝ := refOne*(10+root)/(927/200+8+root)
def crossTwoMinus : ℝ := (21*(927/200)-12-root)/((30-root)*refTwo)
def crossTwoPlus : ℝ := refTwo*(30+root)/(21*(927/200)-12+root)

def oneMinus : ℝ := partF/2+(partG-8*partF)/(2*root)
def onePlus : ℝ := partF/2-(partG-8*partF)/(2*root)
def twoMinus : ℝ := coeffF/42+(coeffG+12*coeffF/21)/(2*root)
def twoPlus : ℝ := coeffF/42-(coeffG+12*coeffF/21)/(2*root)

def rationalPartTwo : ℝ := coeffD*(3/4-1/(927/200-2/3))+
  (coeffE/2)*(9/16-1/(927/200-2/3)^2)

def collectedOne : ℝ := partA*log (927/400)+partB*log (2254/1727)+
  (partC+partF)*log refOne+oneMinus*log crossOneMinus-onePlus*log crossOnePlus+
    F1JointFTC.rationalPart

def collectedTwo : ℝ := coeffA*log (927/400)+coeffB*log (2254/1727)+
  (coeffC+coeffF/21)*log refTwo+twoMinus*log crossTwoMinus-twoPlus*log crossTwoPlus+
    rationalPartTwo

theorem cross_arguments : 1 ≤ crossOneMinus ∧ 1 ≤ crossOnePlus ∧
    1 ≤ crossTwoMinus ∧ 1 ≤ crossTwoPlus := by
  have hr := root_pos
  have hr8 := root_lt_eight
  have hr6 : 6 < root := by nlinarith only [root_sq,root_pos]
  have hm1 : 0 < (10-root)*refOne := mul_pos (by linarith only [hr8]) (by norm_num [refOne])
  have hp1 : 0 < 927/200+8+root := by linarith only [hr]
  have hm2 : 0 < (30-root)*refTwo := mul_pos (by linarith only [hr8]) (by norm_num [refTwo])
  have hp2 : 0 < 21*(927/200)-12+root := by linarith only [hr]
  unfold crossOneMinus crossOnePlus crossTwoMinus crossTwoPlus
  refine ⟨(le_div_iff₀ hm1).mpr ?_,(le_div_iff₀ hp1).mpr ?_,
    (le_div_iff₀ hm2).mpr ?_,(le_div_iff₀ hp2).mpr ?_⟩ <;>
    dsimp [refOne,refTwo] <;> linarith only [hr,hr6]

theorem collectedOne_exact : F1JointFTC.exactMass = collectedOne := by
  obtain ⟨ham,hbp,hap,hbm⟩ := radical_factors_pos
  obtain ⟨hq,hr⟩ := normalized_logs ham hap hbm hbp
    (show 0 < refOne by norm_num [refOne])
  have heq : (927/200+8-root)*(927/200+8+root)/((10-root)*(10+root)) = quadraticRatio := by
    have h0 : (10-root)*(10+root)=(40:ℝ) := by nlinarith only [root_sq]
    rw [h0]
    unfold quadraticRatio
    congr 1
    nlinarith only [root_sq]
  rw [heq] at hq
  have hr' : log radicalRatio = log ((927/200+8-root)/(10-root))-
      log ((927/200+8+root)/(10+root)) := by
    unfold radicalRatio
    rw [log_div (mul_ne_zero ham.ne' hbp.ne') (mul_ne_zero hap.ne' hbm.ne'),
      log_mul ham.ne' hbp.ne',log_mul hap.ne' hbm.ne',
      log_div ham.ne' hbm.ne',log_div hap.ne' hbp.ne']
    ring
  rw [F1JointFTC.collectedMass_exact]
  unfold F1JointFTC.collectedMass collectedOne oneMinus onePlus
  rw [hq,hr',hr]
  change _ = partA*log (927/400)+partB*log (2254/1727)+
    (partC+partF)*log refOne+_ - _ + _
  have he : (1327:ℝ)/800=refOne := by norm_num [refOne]
  rw [he]
  unfold crossOneMinus crossOnePlus
  ring

theorem collectedTwo_exact : exactMass = collectedTwo := by
  have hm : 0 < 21*(927/200)-12-root := by linarith only [root_lt_eight]
  have hp : 0 < 21*(927/200)-12+root := by linarith only [root_pos]
  have hm0 : 0 < 30-root := by linarith only [root_lt_eight]
  have hp0 : 0 < 30+root := by linarith only [root_pos]
  obtain ⟨hq,hr⟩ := normalized_logs hm hp hm0 hp0
    (show 0 < refTwo by norm_num [refTwo])
  have hfact (u : ℝ) : (21*u-12-root)*(21*u-12+root)=
      (21*u-20)^2+16*(21*u-20)+4 := by nlinarith only [root_sq]
  have hq' : log ((21*(927/200)-20)^2+16*(21*(927/200)-20)+4)-
      log ((21*(2:ℝ)-20)^2+16*(21*(2:ℝ)-20)+4) =
      2*log refTwo+log crossTwoMinus-log crossTwoPlus := by
    rw [← log_div (by norm_num : ((21*((927:ℝ)/200)-20)^2+16*(21*(927/200)-20)+4) ≠ 0)
      (by norm_num : ((21*(2:ℝ)-20)^2+16*(21*(2:ℝ)-20)+4) ≠ 0)]
    rw [← hfact,← hfact]
    convert hq using 1 <;> norm_num [crossTwoMinus,crossTwoPlus]
  have hr' : (log (21*(927/200)-20+8-root)-log (21*(927/200)-20+8+root))-
      (log (21*(2:ℝ)-20+8-root)-log (21*(2:ℝ)-20+8+root)) =
      log crossTwoMinus+log crossTwoPlus := by
    have he1 : 21*((927:ℝ)/200)-20+8=21*(927/200)-12 := by ring
    rw [he1]
    norm_num only [show 21*(2:ℝ)-20+8=30 by norm_num]
    rw [log_div hm.ne' hm0.ne',log_div hp.ne' hp0.ne'] at hr
    unfold crossTwoMinus crossTwoPlus
    convert hr using 1
    ring
  have hA : log ((927:ℝ)/400)=log (927/200)-log 2 := by
    rw [← log_div (by norm_num : (927:ℝ)/200 ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  have hB : log ((2254:ℝ)/1727)=log (927/200+1327/200)-log (2+1327/200) := by
    rw [← log_div (by norm_num : (927:ℝ)/200+1327/200 ≠ 0)
      (by norm_num : (2:ℝ)+1327/200 ≠ 0)]
    norm_num
  have hC : log refTwo=log (927/200-2/3)-log ((2:ℝ)-2/3) := by
    rw [← log_div (by norm_num : (927:ℝ)/200-2/3 ≠ 0)
      (by norm_num : (2:ℝ)-2/3 ≠ 0)]
    norm_num [refTwo]
  have hquad : affinePrimitive coeffF coeffG (927/200)-affinePrimitive coeffF coeffG 2 =
      (coeffF/21)*log refTwo+twoMinus*log crossTwoMinus-twoPlus*log crossTwoPlus := by
    unfold affinePrimitive F1JointFTC.quadraticPrimitive twoMinus twoPlus
    linear_combination (coeffF/21/2)*hq'+((coeffG+20*coeffF/21-8*(coeffF/21))/(2*root))*hr'
  unfold exactMass primitive collectedTwo rationalPartTwo
  rw [hA,hB,hC]
  rw [hC] at hquad
  unfold polePrimitive
  simp only [sub_zero,sub_neg_eq_add,zero_div,sub_zero]
  linear_combination hquad

end F1ActualSecondFTC
