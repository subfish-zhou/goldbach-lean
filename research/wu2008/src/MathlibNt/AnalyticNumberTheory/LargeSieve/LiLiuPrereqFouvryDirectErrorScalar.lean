import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectAlphaMass
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectAnalyticLosses
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectGlobalPayment

/-! Scalar endgame, with every remaining input labelled. This is not the
unconditional distribution theorem until the actual prefix producer is supplied. -/
noncomputable section
open Classical Finset Filter
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem direct_error_scalar {M T x A J Y V P Cα Ccost Ccell δ η ε : ℝ}
    (hM : 0 ≤ M) (_hT : 0 ≤ T) (hx : 0 < x)
    (_hA : 0 ≤ A) (hJ : 0 ≤ J) (hY : 0 ≤ Y) (hV : 0 ≤ V) (hP : 0 ≤ P)
    (hCα : 0 ≤ Cα) (hCcost : 0 ≤ Ccost) (_hCcell : 0 ≤ Ccell)
    (hMT : x = 4*M*T)
    (halpha : A ≤ Cα*M*x^δ)
    (hcost : J*Y*V ≤ Ccost*x^(12*η+δ))
    (hcell : P ≤ Ccell*T^2*x^(δ-ε/2)) :
    3072*M*A*J*Y*V*P ≤
      (192*Cα*Ccost*Ccell)*x^2*x^(12*η+3*δ-ε/2) := by
  have he : 3072*M*A*J*Y*V*P = 3072*M*A*(J*Y*V)*P := by ring
  rw [he]
  calc
    _ ≤ 3072*M*(Cα*M*x^δ)*(Ccost*x^(12*η+δ))*(Ccell*T^2*x^(δ-ε/2)) := by gcongr
    _ = (192*Cα*Ccost*Ccell)*(4*M*T)^2 *
        (x^δ*x^(12*η+δ)*x^(δ-ε/2)) := by ring
    _ = _ := by
      rw [← hMT, ← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 2
      ring

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
