import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectAlphaMass
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectAnalyticLosses
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectGlobalPayment

/-! Scalar endgame, with every remaining input labelled. This is not the
unconditional distribution theorem until the actual prefix producer is supplied. -/
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry


/-- Uniform power saving implies any requested logarithmic saving. -/
theorem direct_power_to_log (C : ℝ) (hC : 0 ≤ C) (A : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, C*x^2*x^(-ε) ≤ x^2/Real.log x^A := by
  filter_upwards [betaPayment_eventually_log_mul_rpow_le C hC A
      (show -ε < (0 : ℝ) by linarith),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    eventually_ge_atTop (1 : ℝ)] with x hp hlog hx
  have hx0 : 0 < x := by linarith
  have hl0 : 0 < Real.log x := by linarith
  have hs : C*Real.log x^A*x^(-ε) ≤ 1 := by
    apply le_trans _ (by simpa using hp)
    gcongr
    linarith
  apply (le_div_iff₀ (pow_pos hl0 A)).2
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg x)
  nlinarith

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
