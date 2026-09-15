import F1BFullResidual

noncomputable section
open Real Set FirstIntegralRecovery FirstCRationalPayment
open Wu2008DoubleSieve SharpLogRecurrence F1FullRecoveryPayment
open F1RemainingRecovery F1UnpaidRecovery F1SecondLogRecovery
namespace F1BFullFTC

/-- Only the original once-only split, not a further split of its factors. -/
def splitGap (x : ℝ) : ℝ := lowerGapPayment ((1+x)/2)+lowerGapPayment (2*x/(1+x))
def splitFresh (x : ℝ) : ℝ := F1LowerResidual.payment ((1+x)/2)+
  F1LowerResidual.payment (2*x/(1+x))

theorem split_retained {x : ℝ} (hx : 1 ≤ x) :
    splitGap x+splitFresh x ≤ log x-splitL x := by
  have h1 := F1LowerResidual.payment_le (split_arguments hx).1
  have h2 := F1LowerResidual.payment_le (split_arguments hx).2
  rw [split_log_identity hx]
  unfold splitGap splitFresh splitL
  linarith only [h1,h2]

theorem fresh_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ splitFresh x := by
  have h (t : ℝ) (ht : 1 ≤ t) : 0 ≤ F1LowerResidual.payment t := by
    unfold F1LowerResidual.payment F1LowerResidual.denom
    have ht0 : 0 < t := by linarith
    have htm : 0 ≤ t-1 := by linarith
    positivity
  exact add_nonneg (h _ (split_arguments hx).1) (h _ (split_arguments hx).2)

theorem gap_rational {x : ℝ} (hx : 1 ≤ x) : splitGap x =
    (x-1)^5/((x+3)^3*(x^2+18*x+21))+
      (x-1)^5/((3*x+1)^3*(21*x^2+18*x+1)) := by
  have hx0 : 0 < x := by linarith
  unfold splitGap
  rw [lower_error_rational (split_arguments hx).1,lower_error_rational (split_arguments hx).2]
  field_simp
  ring

theorem gap_nonneg {x : ℝ} (hx : 1 ≤ x) : 0 ≤ splitGap x := by
  rw [gap_rational hx]
  have hx0 : 0 < x := by linarith
  have hm : 0 ≤ x-1 := by linarith
  positivity

def linearA (u : ℝ) : ℝ := 2*(u-2)/(u+2)+2*(u-2)/(3*u-2)
def linearB (u : ℝ) : ℝ := 2*((1327:ℝ)/200-2-u)/((1327:ℝ)/200+u)

theorem a_paid_identity {u : ℝ} (hu : 2 ≤ u) :
    splitGap (u-1)/u*linearB u = F1JointFTC.kernel u+F1ActualSecondFTC.kernel u := by
  rw [gap_rational (show 1 ≤ u-1 by linarith)]
  have h1 : (u-1-1)^5/((u-1+3)^3*((u-1)^2+18*(u-1)+21)) =
      (u-2)^5/((u+2)^3*(u^2+16*u+4)) := by congr 1 <;> ring
  have h2 : (u-1-1)^5/((3*(u-1)+1)^3*(21*(u-1)^2+18*(u-1)+1)) =
      (u-2)^5/((3*u-2)^3*(21*u^2-24*u+4)) := by congr 1 <;> ring
  rw [h1,h2,add_div,add_mul]
  exact congrArg₂ (·+·) (F1ActualSecondFTC.first_identity u) (F1ActualSecondFTC.factor_identity u)

theorem b_paid_identity {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    linearA u/u*splitGap (((1327:ℝ)/200-1)/(u+1)) = kernelOne u+kernelTwo u := by
  have hu' : u ∈ Icc 2 ((1327:ℝ)/200-2) := by constructor <;> linarith [hu.1,hu.2]
  have hu0 : 0 < u := by linarith [hu.1]
  rw [gap_rational (ratio_ge_one hu')]
  norm_num only [show (1327:ℝ)/200-1=1127/200 by norm_num]
  rw [scaled_error_one (by norm_num) (by linarith [hu.1]),
    scaled_error_two (by norm_num) (by linarith [hu.1])]
  have ht : 3*u-2 ≠ 0 := by linarith [hu.1]
  obtain ⟨hd1,hd2,_,_⟩ := denominators_pos hu.1
  unfold linearA kernelOne kernelTwo denomOne denomTwo weight
  change _ = 8*((u-2)*(927/200-u)^5)/((u+2)*(3*u-2)*errorDenomOne u)+
    8*((u-2)*(927/200-u)^5)/((u+2)*(3*u-2)*errorDenomTwo u)
  have he : (1127:ℝ)/200-(u+1)=927/200-u := by ring
  rw [he]
  change _/u*((927/200-u)^5/errorDenomOne u+(927/200-u)^5/errorDenomTwo u)=_
  field_simp [ht,hu0.ne',hd1.ne',hd2.ne',show u+2 ≠ 0 by linarith [hu.1]]
  ring_nf
  field_simp [show -2+u*3 ≠ 0 by linarith [hu.1]]
  ring

/-- Existing lower-residual payments still unpaid after the four exact FTC kernels. -/
def freshA (u : ℝ) : ℝ := splitFresh (u-1)/u*linearB u
def freshB (u : ℝ) : ℝ := linearA u/u*splitFresh (((1327:ℝ)/200-1)/(u+1))

theorem fresh_covers {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    0 ≤ freshA u ∧ freshA u ≤ unpaidA u ∧ 0 ≤ freshB u ∧ freshB u ≤ unpaidB u := by
  have hx : 1 ≤ u-1 := by linarith [hu.1]
  have hu' : u ∈ Icc 2 ((1327:ℝ)/200-2) := by constructor <;> linarith [hu.1,hu.2]
  have hr := ratio_ge_one hu'
  have hu0 : 0 < u := by linarith [hu.1]
  have hla : 0 ≤ linearA u := by
    unfold linearA
    exact add_nonneg (div_nonneg (by linarith [hu.1]) (by linarith [hu.1]))
      (div_nonneg (by linarith [hu.1]) (by linarith [hu.1]))
  have hlb : 0 ≤ linearB u := by unfold linearB; exact div_nonneg (by linarith [hu.2]) (by linarith [hu.1])
  have hfa := fresh_nonneg hx
  have hfb := fresh_nonneg hr
  have hsa := split_retained hx
  have hsb := split_retained hr
  have hba := gap_nonneg hx
  have hbb := gap_nonneg hr
  have hlogb := ratio_log_payment hu'
  have hslina := splitL_linear hu.1
  change linearB u ≤ _ at hlogb
  change linearA u ≤ _ at hslina
  have hap := mul_le_mul (div_le_div_of_nonneg_right hsa hu0.le) hlogb hlb
    (div_nonneg (sub_nonneg.mpr (splitL_le_log hx)) hu0.le)
  have hbp := mul_le_mul (div_le_div_of_nonneg_right hslina hu0.le) hsb
    (add_nonneg hbb hfb) (div_nonneg (splitL_nonneg hx) hu0.le)
  rw [add_div,add_mul,a_paid_identity hu.1] at hap
  rw [mul_add,b_paid_identity hu] at hbp
  refine ⟨mul_nonneg (div_nonneg hfa hu0.le) hlb,?_,
    mul_nonneg (div_nonneg hla hu0.le) hfb,?_⟩
  · unfold freshA unpaidA
    linarith only [hap]
  · unfold freshB unpaidB secondExact
    linarith only [hbp]

end F1BFullFTC
