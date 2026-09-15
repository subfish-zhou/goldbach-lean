import F1JointAssembly

noncomputable section
open Real Set MeasureTheory FirstCRationalPayment F1RemainingRecovery
open Wu2008DoubleSieve SharpLogRecurrence
namespace F1JointFTC

def radicalRatio : ℝ := ((927/200+8-root)*(10+root))/((927/200+8+root)*(10-root))
def quadraticRatio : ℝ := ((927/200)^2+16*(927/200)+4)/40
def rationalPart : ℝ := partD*(1/4-1/(927/200+2))+
  (partE/2)*(1/16-1/(927/200+2)^2)
def collectedMass : ℝ :=
  partA*log (927/400)+partB*log (2254/1727)+partC*log (1327/800)+
    (partF/2)*log quadraticRatio+((partG-8*partF)/(2*root))*log radicalRatio+rationalPart

theorem radical_factors_pos :
    0 < 927/200+8-root ∧ 0 < 10+root ∧ 0 < 927/200+8+root ∧ 0 < 10-root := by
  have h0 := root_pos
  have h1 := root_lt_eight
  constructor
  · linarith only [h1]
  constructor
  · linarith only [h0]
  constructor
  · linarith only [h0]
  · linarith only [h1]

theorem collectedMass_exact : exactMass = collectedMass := by
  have hA : log ((927:ℝ)/400)=log (927/200)-log 2 := by
    rw [← log_div (by norm_num : (927:ℝ)/200 ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  have hB : log ((2254:ℝ)/1727)=log (927/200+1327/200)-log (2+1327/200) := by
    rw [← log_div (by norm_num : (927:ℝ)/200+1327/200 ≠ 0)
      (by norm_num : (2:ℝ)+1327/200 ≠ 0)]
    norm_num
  have hC : log ((1327:ℝ)/800)=log (927/200+2)-log (2+2) := by
    rw [← log_div (by norm_num : (927:ℝ)/200+2 ≠ 0) (by norm_num : (2:ℝ)+2 ≠ 0)]
    norm_num
  have hQ : log quadraticRatio=log ((927/200)^2+16*(927/200)+4)-log ((2:ℝ)^2+16*2+4) := by
    rw [← log_div (by norm_num : ((927:ℝ)/200)^2+16*(927/200)+4 ≠ 0)
      (by norm_num : (2:ℝ)^2+16*2+4 ≠ 0)]
    norm_num [quadraticRatio]
  obtain ⟨hp,hq,hr,hs⟩ := radical_factors_pos
  have hR : log radicalRatio =
      (log (927/200+8-root)-log (927/200+8+root))-
        (log (2+8-root)-log (2+8+root)) := by
    unfold radicalRatio
    rw [log_div (mul_ne_zero hp.ne' hq.ne') (mul_ne_zero hr.ne' hs.ne'),
      log_mul hp.ne' hq.ne',log_mul hr.ne' hs.ne']
    norm_num
    ring
  unfold exactMass primitive quadraticPrimitive polePrimitive collectedMass rationalPart
  rw [hA,hB,hC,hQ,hR]
  simp only [sub_zero,sub_neg_eq_add,zero_div,sub_zero]
  ring

theorem radicalRatio_ge_one : 1 ≤ radicalRatio := by
  obtain ⟨_,_,hp,hq⟩ := radical_factors_pos
  unfold radicalRatio
  apply (le_div_iff₀ (mul_pos hp hq)).mpr
  nlinarith only [root_pos]

/-- All arguments below are forced endpoint ratios of the original primitive. -/
def collectedLower : ℝ :=
  partA*JointLogTotalComparison.V (927/400)+partB*lowerLog (2254/1727)+
    partC*JointLogTotalComparison.V (1327/800)+
    (partF/2)*JointLogTotalComparison.V quadraticRatio+
    ((partG-8*partF)/(2*root))*lowerLog radicalRatio+rationalPart

theorem collectedLower_le_exactMass : collectedLower ≤ exactMass := by
  rw [collectedMass_exact]
  have hA := mul_le_mul_of_nonpos_left
    (JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 927/400))
    (show partA ≤ 0 by norm_num [partA])
  have hB := mul_le_mul_of_nonneg_left (log_lower (by norm_num : (1:ℝ) ≤ 2254/1727))
    (show 0 ≤ partB by norm_num [partB])
  have hC := mul_le_mul_of_nonpos_left
    (JointLogTotalComparison.log_le_V (by norm_num : (1:ℝ) ≤ 1327/800))
    (show partC ≤ 0 by norm_num [partC])
  have hQ := mul_le_mul_of_nonpos_left
    (JointLogTotalComparison.log_le_V (show 1 ≤ quadraticRatio by norm_num [quadraticRatio]))
    (show partF/2 ≤ 0 by norm_num [partF])
  have hpos : 0 ≤ (partG-8*partF)/(2*root) := by
    apply div_nonneg
    · norm_num [partG,partF]
    · exact mul_nonneg (by norm_num) root_pos.le
  have hR := mul_le_mul_of_nonneg_left (log_lower radicalRatio_ge_one) hpos
  unfold collectedLower collectedMass
  linarith only [hA,hB,hC,hQ,hR]

end F1JointFTC
