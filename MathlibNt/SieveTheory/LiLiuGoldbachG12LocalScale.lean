import MathlibNt.SieveTheory.LiLiuPrereqWFExternalParameters
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Uniform local C2 scales. The ambient scale and the local scale stay distinct. -/
namespace G12LocalScale
open Real Filter
open scoped Topology

noncomputable def nu (x T : ℝ) : ℝ := log T / log x
noncomputable def level (x T ζ : ℝ) : ℝ := x ^ ((5 - 5 * nu x T) / 9 - ζ)

theorem log_level {x T ζ : ℝ} (hx : 1 < x) :
    log (level x T ζ) = (5 / 9 - ζ) * log x - 5 / 9 * log T := by
  rw [level, Real.log_rpow (by linarith)]
  unfold nu
  field_simp [(Real.log_pos hx).ne']
  ring

theorem recover_T {x T : ℝ} (hx : 1 < x) (hT : 0 < T) :
    x ^ nu x T = T := by
  rw [nu, Real.rpow_def_of_pos (by linarith)]
  rw [mul_div_cancel₀ _ (Real.log_pos hx).ne', Real.exp_log hT]

/-- Pure algebraic distortion estimate, separated from the uniform cutoff. -/
theorem logarithmic_geometry {L X Y ζ : ℝ}
    (hL : 0 < L) (hz : 0 < ζ) (hzsmall : ζ ≤ 1 / 100)
    (hXlo : (1 - ζ / 4) * L ≤ X) (hXhi : X ≤ (1 + ζ / 4) * L)
    (hYlo : (4 / 53 - ζ / 4) * L ≤ Y) (hYhi : Y ≤ (1 / 10) * L) :
    0 < X ∧ ζ ≤ Y / X ∧ Y / X ≤ 1 / 10 + ζ / 10 ∧
      L / 3 ≤ (5 / 9 - ζ) * X - 5 / 9 * Y ∧
      (5 / 9 - ζ) * X - 5 / 9 * Y ≤ L := by
  have hx : 0 < X := by nlinarith
  have hzL : 0 < ζ * L := mul_pos hz hL
  have hlo := mul_le_mul_of_nonneg_left hXlo (show 0 ≤ 5 / 9 - ζ by linarith)
  have hhi := mul_le_mul_of_nonneg_left hXhi (show 0 ≤ 5 / 9 - ζ by linarith)
  have hz2 : ζ * ζ * L ≤ (1 / 100) * ζ * L := by nlinarith [mul_nonneg (show 0 ≤ 1 / 100 - ζ by linarith) hzL.le]
  refine ⟨hx, (le_div_iff₀ hx).2 ?_, (div_le_iff₀ hx).2 ?_, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left hXhi hz.le]
  · nlinarith [mul_le_mul_of_nonneg_left hXlo (show 0 ≤ 1 / 10 + ζ / 10 by positivity)]
  · nlinarith
  · nlinarith

/-- The reciprocal distortion costs at most `48 * ζ`, uniformly in the endpoint. -/
theorem reciprocal_bridge {a b ζ δ : ℝ}
    (ha : 1 / 2 ≤ a) (hb : 1 / 3 ≤ b)
    (hab : a - 2 * ζ ≤ b) (hδ : 0 ≤ δ) (hsmall : 48 * ζ ≤ δ) :
    4 / b ≤ 4 / a + δ := by
  have hap : 0 < a := by linarith
  have hbp : 0 < b := by linarith
  have hp : 1 / 6 ≤ a * b := by nlinarith [mul_nonneg (show 0 ≤ a - 1 / 2 by linarith) (show 0 ≤ b - 1 / 3 by linarith)]
  have hd := mul_le_mul_of_nonneg_left hp hδ
  apply (div_le_iff₀ hbp).2
  apply (mul_le_mul_iff_right₀ hap).mp
  have heq : a * ((4 / a + δ) * b) = 4 * b + δ * (a * b) := by field_simp
  rw [heq]
  nlinarith
end G12LocalScale
