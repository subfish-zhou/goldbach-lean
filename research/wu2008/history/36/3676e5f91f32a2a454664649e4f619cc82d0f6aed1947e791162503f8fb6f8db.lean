import MathlibNt.Wu2008DoubleSieve.Omega3XNormalization

/-!
# Paying the X approximation on the original Theta scale

The same reciprocal mass and the full C(N) occur on both sides.
No uniform upper bound for the singular series is used.
-/

namespace Wu2008DoubleSieve

open Real

theorem omega3X_scaled_error_le {i k N : ℕ} {δ Δ ε K : ℝ} {V : Fin i → ℝ}
    (hN : 4 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hε : 0 ≤ ε) (hK : 0 ≤ K) :
    (ε * ((N : ℝ) / log N) *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) *
      (K * wuSingularSeries N / log N) ≤
      (ε * K / 2) *
        boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  calc
    _ = (ε * K / 2) * (2 * wuSingularSeries N * (N : ℝ) / log N ^ 2 *
        boxConvolutionReciprocalMass (convolutionWuWindows N Δ V)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (omega3_source_theta_lower_singular hN hδ hδhi hb) (by positivity)

theorem omega3X_fixed_density_factor_pos {δ ρ : ℝ}
    (hδhi : δ < 1 / 2) (hρ : 0 < ρ) :
    0 < (1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
      (8 / (1 - 2 * δ)) := by
  have : 0 < 1 - 2 * δ := by linarith
  positivity

end Wu2008DoubleSieve
