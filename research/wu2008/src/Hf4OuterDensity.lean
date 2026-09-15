import Hf4OuterResidual

noncomputable section
namespace Hf4Outer
open Real Set SigmaVariableOuterPayment SigmaVariableFull TerminalE

/-- All four collected coefficients survive, with the negative coefficient reversed. -/
theorem mass_loss_identity {t : ℝ} (ht : 1 ≤ t) :
    collectedMass t-paidMass t =
      (-logZeroCoeff (-(t+1)))*(RemainingHf.splitUpper (zeroRatio t)-log (zeroRatio t))+
      logNegCoeff (-(t+1))*(log (negRatio t)-RemainingHf.splitLower (negRatio t))+
      logQuadCoeff (-(t+1))*(log (quadRatio t)-RemainingHf.splitLower (quadRatio t))+
      logRadCoeff (-(t+1))*(log (radRatio t)-RemainingHf.splitLower (radRatio t)) := by
  rw [mass_regrouped ht]
  unfold paidMass
  ring

/-- Retain the original negative atom; do not assert positivity of a signed log atom. -/
theorem negative_atom_payment_le {t : ℝ} (ht : t ∈ Icc 1 3) :
    (-logZeroCoeff (-(t+1)))*upperPayment (Wu04FactorEnvelopes.leftFactor (zeroRatio t)) ≤
      collectedMass t-paidMass t := by
  have h0 := mul_le_mul_of_nonneg_left (splitUpper_loss_lower (zeroRatio_ge ht.1))
    (neg_nonneg.mpr (zero_coefficient_neg ht.1).le)
  have h1 := mul_nonneg (neg_coefficient_pos ht.1).le
    (sub_nonneg.mpr (RemainingHf.splitLower_le (negRatio_ge ht.1)))
  have hq := mul_nonneg (quad_coefficient_pos ht).le
    (sub_nonneg.mpr (RemainingHf.splitLower_le (quadRatio_ge ht.1)))
  have hr := mul_nonneg (rad_coefficient_pos ht).le
    (sub_nonneg.mpr (RemainingHf.splitLower_le (radRatio_ge ht.1)))
  rw [mass_loss_identity ht.1]
  linarith only [h0,h1,hq,hr]

theorem zero_coefficient_magnitude {t : ℝ} (ht : 1 ≤ t) :
    10 ≤ -logZeroCoeff (-(t+1)) := by
  rw [zero_coefficient_formula ht, neg_div, neg_neg]
  apply (le_div_iff₀ (by positivity : 0 < 210*(t+1)^2)).mpr
  have ht0 : 0 ≤ t := by linarith
  nlinarith only [sq_nonneg t,ht0]

/-- A new outer density, independent of the already-paid inner variation. -/
def outerDensity (t : ℝ) : ℝ := (t-1)^8/(336*t*(t+5)^3*(t+11)^4)

theorem outerDensity_factorization {t : ℝ} (ht : 1 ≤ t) :
    outerDensity t = 10*upperPayment (Wu04FactorEnvelopes.leftFactor (zeroRatio t))/t := by
  have ht0 : t ≠ 0 := by linarith
  have h5 : t+5 ≠ 0 := by linarith
  have h11 : t+11 ≠ 0 := by linarith
  unfold outerDensity upperPayment Wu04FactorEnvelopes.leftFactor zeroRatio
  field_simp
  ring

/-- Quantitative comparison with actual weight minus the frozen 23-block paid weight. -/
theorem outerDensity_le_loss {t : ℝ} (ht : t ∈ Icc 1 3) :
    outerDensity t ≤ SigmaVariableFull.weight t-paidWeight t := by
  have hp := upperPayment_nonneg (Wu04FactorEnvelopes.factors (zeroRatio_ge ht.1)).1
  have hc := mul_le_mul_of_nonneg_right (zero_coefficient_magnitude ht.1) hp
  have hm := hc.trans (negative_atom_payment_le ht)
  rw [outerDensity_factorization ht.1]
  unfold SigmaVariableFull.weight paidWeight
  rw [← collectedMass_identity, ← sub_div]
  exact div_le_div_of_nonneg_right hm (by linarith [ht.1])

/-- Freeze only the upper endpoint of the original outer cell, with no new cut. -/
def cellDensity (b t : ℝ) : ℝ := (t-1)^8/(336*b*(b+5)^3*(b+11)^4)

theorem cellDensity_le_outer {t b : ℝ} (ht : 1 ≤ t) (hb : t ≤ b) :
    cellDensity b t ≤ outerDensity t := by
  have ht0 : 0 < t := by linarith
  have hb0 : 0 < b := ht0.trans_le hb
  unfold cellDensity outerDensity
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr

theorem cellDensity_le_loss {t b : ℝ} (ht : t ∈ Icc 1 3) (hb : t ≤ b) :
    cellDensity b t ≤ SigmaVariableFull.weight t-paidWeight t :=
  (cellDensity_le_outer ht.1 hb).trans (outerDensity_le_loss ht)

end Hf4Outer
