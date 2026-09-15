import RemainingHfLog
namespace RemainingHf
open Real Wu2008DoubleSieve SharpLogRecurrence JointLogTotalComparison
open FirstErrorFullPayment F1FullRecoveryPayment
noncomputable section

def beta (x : ℝ) : ℝ := 6*x/(x^2+8*x+1)

theorem beta_antitone {x y : ℝ} (hx : 1 ≤ x) (hxy : x ≤ y) : beta y ≤ beta x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hq : 0 < x^2+8*x+1 := by positivity
  have hr : 0 < y^2+8*y+1 := by positivity
  unfold beta
  apply (div_le_div_iff₀ hr hq).mpr
  have hprod : 0 ≤ (y-x)*(x*y-1) := by
    apply mul_nonneg (sub_nonneg.mpr hxy)
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ y-1 by linarith)]
  nlinarith only [hprod]

def cellScale (S b : ℝ) : ℝ := (7/4)*beta ((b+1)/(S-1))

def residualDenom (S b : ℝ) : ℝ :=
  210*b*(b+1)^2*(b+S)^4*((b+1)^2+8*(b+1)*(S-1)+(S-1)^2)

def residualDensity (S b t : ℝ) : ℝ :=
  (t+2-S)^7*(5*(t+2-S)+12*(S-1))/residualDenom S b

def residualPrimitive (S b t : ℝ) : ℝ :=
  ((5/9)*(t+2-S)^9+(3*(S-1)/2)*(t+2-S)^8)/residualDenom S b

theorem residual_identity {S t : ℝ} (hS : 3 ≤ S) (ht : S-2 ≤ t) :
    F1LowerResidual.payment ((t+1)/(S-1))/t=residualDensity S t t := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < S-1 := by linarith
  have ht1 : 0 < t+1 := by positivity
  have hts : 0 < t+S := by linarith
  have hq : 0 < (t+1)^2+8*(t+1)*(S-1)+(S-1)^2 := by positivity
  unfold F1LowerResidual.payment F1LowerResidual.denom residualDensity residualDenom
  field_simp
  ring

theorem residualDensity_le {S b t : ℝ} (hS : 3 ≤ S) (ht : S-2 ≤ t) (htb : t ≤ b) :
    residualDensity S b t ≤ F1LowerResidual.payment ((t+1)/(S-1))/t := by
  rw [residual_identity hS ht]
  have ht0 : 0 < t := by linarith
  have hb0 : 0 < b := by linarith
  have hs0 : 0 < S-1 := by linarith
  have hd : 0 < residualDenom S t := by unfold residualDenom; positivity
  have hden : residualDenom S t ≤ residualDenom S b := by
    unfold residualDenom
    gcongr
  unfold residualDensity
  apply div_le_div_of_nonneg_left _ hd hden
  exact mul_nonneg (pow_nonneg (by linarith) _) (by linarith)

theorem residualPrimitive_deriv (S b t : ℝ) :
    HasDerivAt (residualPrimitive S b) (residualDensity S b t) t := by
  have h := ((hasDerivAt_id t).add_const 2).sub_const S
  convert ((((h.pow 9).const_mul (5/9)).add
    ((h.pow 8).const_mul (3*(S-1)/2))).div_const (residualDenom S b)) using 1 <;>
    first | rfl | (dsimp [residualPrimitive,residualDensity]; ring)

theorem paidDensity_le {S b t : ℝ} (hS : 3 ≤ S) (ht : S-2 ≤ t) (htb : t ≤ b) :
    lowerLog ((t+1)/(S-1))/t+cellScale S b*errorDensity S t+residualDensity S b t ≤
      log ((t+1)/(S-1))/t := by
  have ht0 : 0 < t := by linarith
  have hs0 : 0 < S-1 := by linarith
  have hx : 1 ≤ (t+1)/(S-1) := (one_le_div hs0).mpr (by linarith)
  have hxy : (t+1)/(S-1) ≤ (b+1)/(S-1) := by gcongr
  have hg : 0 ≤ upperLog ((t+1)/(S-1))-lowerLog ((t+1)/(S-1)) := by
    rw [OriginalFirstErrorRecovery.envelope_gap (by positivity)]
    positivity
  have hc := mul_le_mul_of_nonneg_right (beta_antitone hx hxy) hg
  have hr := F1LowerResidual.payment_le hx
  have hm := div_le_div_of_nonneg_right hc ht0.le
  have hp := div_le_div_of_nonneg_right hr ht0.le
  have hd := residualDensity_le hS ht htb
  unfold cellScale errorDensity beta lowerGapPayment at *
  simp only [div_eq_mul_inv] at *
  ring_nf at hm hp hd ⊢
  linarith only [hm,hp,hd]
end
end RemainingHf
