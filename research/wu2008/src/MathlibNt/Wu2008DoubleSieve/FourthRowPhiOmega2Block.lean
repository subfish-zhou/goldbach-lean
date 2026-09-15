import MathlibNt.Wu2008DoubleSieve.FourthRowPhiOmega2

/-!
# The remaining fourth-row Phi/Omega2 block

All coefficients, counts, gains, and source boxes are the old actual objects.
The four independent count estimates receive epsilon/8: their absolute
multipliers are 4, 1, 2, 1. No division by Theta is used.
-/

namespace Wu2008DoubleSieve
namespace FourthRowPhiOmega2

open Set Real MeasureTheory
open scoped Interval

/-- The first literal logarithm-plus-final-gain identity. -/
theorem J_five_halves_eq_log (δ : ℝ) :
    J δ (5 / 2) (103 / 25) =
      ∫ u in (1 - 1 / (5 / 2 : ℝ))..(1 - 1 / (103 / 25 : ℝ)),
        (log ((103 / 25 : ℝ) * u - 1) +
          wuImprovementLimit false δ ((103 / 25 : ℝ) * u)) / (u * (1 - u)) := by
  exact J_eq_log (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The second literal logarithm-plus-final-gain identity. -/
theorem J_291_eq_log (δ : ℝ) :
    J δ (291 / 100) (103 / 25) =
      ∫ u in (1 - 1 / (291 / 100 : ℝ))..(1 - 1 / (103 / 25 : ℝ)),
        (log ((103 / 25 : ℝ) * u - 1) +
          wuImprovementLimit false δ ((103 / 25 : ℝ) * u)) / (u * (1 - u)) := by
  exact J_eq_log (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Both the literal coefficient and logarithmic integrands are integrable
on each of the two actual intervals. No regularity of the gain is assumed. -/
theorem actual_integrability {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    (∀ x ∈ ({(5 / 2 : ℝ), 291 / 100} : Set ℝ),
      IntervalIntegrable (fun u =>
        (wuLowerCoefficient ((103 / 25 : ℝ) * u) +
          wuImprovementLimit false δ ((103 / 25 : ℝ) * u)) / (u * (1 - u)))
        volume (1 - 1 / x) (1 - 1 / (103 / 25 : ℝ))) ∧
    (∀ x ∈ ({(5 / 2 : ℝ), 291 / 100} : Set ℝ),
      IntervalIntegrable (fun u =>
        (log ((103 / 25 : ℝ) * u - 1) +
          wuImprovementLimit false δ ((103 / 25 : ℝ) * u)) / (u * (1 - u)))
        volume (1 - 1 / x) (1 - 1 / (103 / 25 : ℝ))) := by
  have hδhalf : δ < 1 / 2 := by linarith
  constructor
  · intro x hx
    rcases hx with (rfl | rfl)
    · exact limit_intervalIntegrable hδ hδhalf (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
    · exact limit_intervalIntegrable hδ hδhalf (by norm_num) (by norm_num)
        (by norm_num) (by norm_num)
  · intro x hx
    have hs : 2 ≤ x := by rcases hx with (rfl | rfl) <;> norm_num
    have hst : x ≤ (103 / 25 : ℝ) := by rcases hx with (rfl | rfl) <;> norm_num
    have hratio : 2 ≤ (103 / 25 : ℝ) - (103 / 25 : ℝ) / x := by
      rcases hx with (rfl | rfl) <;> norm_num
    simpa only [add_div] using
      (firstFunctionalGain_log_intervalIntegrable hs hst (by norm_num)
        (by norm_num) hratio).add
        (firstFunctionalGain_limit_intervalIntegrable hδ hδhalf hs hst
          (by norm_num) (by norm_num))

/-- The first actual Omega2 lower-bound instance. -/
theorem omega2_five_halves_actual_limit_lower (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        (J δ (5 / 2) (103 / 25) - ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuOmega2Sum N δ (5 / 2) (103 / 25) (convolutionWuWindows N Δ V) := by
  exact omega2_actual_limit_lower k hk hδ hδhi (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hε

/-- The second actual Omega2 lower-bound instance. -/
theorem omega2_291_actual_limit_lower (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        (J δ (291 / 100) (103 / 25) - ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤
        wuOmega2Sum N δ (291 / 100) (103 / 25) (convolutionWuWindows N Δ V) := by
  exact omega2_actual_limit_lower k hk hδ hδhi (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hε

/-- Actual limiting H/h upper bound for precisely the remaining Phi/Omega2
block. No Psi2 base-term elimination, new count, or kernel is part of it. -/
theorem actual_limit_block (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        4 * wuBoxPhi N δ (convolutionWuWindows N Δ V) (103 / 25) +
          wuBoxPhi N δ (convolutionWuWindows N Δ V) (89 / 25) -
          2 * wuOmega2Sum N δ (5 / 2) (103 / 25) (convolutionWuWindows N Δ V) -
          wuOmega2Sum N δ (291 / 100) (103 / 25) (convolutionWuWindows N Δ V) ≤
        (4 * wuUpperCoefficient (103 / 25) + wuUpperCoefficient (89 / 25) -
          4 * wuImprovementLimit true δ (103 / 25) -
          wuImprovementLimit true δ (89 / 25) -
          2 * J δ (5 / 2) (103 / 25) - J δ (291 / 100) (103 / 25) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hδhalf : δ < 1 / 2 := by linarith
  have heps : 0 < ε / 8 := by positivity
  obtain ⟨P, hP4, hP⟩ := phi_actual_limit_upper k hk hδ hδhalf
    (show (1 : ℝ) ≤ 103 / 25 by norm_num) (by norm_num) heps
  obtain ⟨Q, _, hQ⟩ := phi_actual_limit_upper k hk hδ hδhalf
    (show (1 : ℝ) ≤ 89 / 25 by norm_num) (by norm_num) heps
  obtain ⟨R, _, hR⟩ := omega2_five_halves_actual_limit_lower k hk hδ hδhi heps
  obtain ⟨U, _, hU⟩ := omega2_291_actual_limit_lower k hk hδ hδhi heps
  let T := max (max P Q) (max R U)
  have hPT : P ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hQT : Q ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hRT : R ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hUT : U ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T, hP4.trans hPT, ?_⟩
  intro N hN he i Δ V hb
  have hp := hP N (hPT.trans hN) he i Δ V hb
  have hq := hQ N (hQT.trans hN) he i Δ V hb
  have hr := hR N (hRT.trans hN) he i Δ V hb
  have hu := hU N (hUT.trans hN) he i Δ V hb
  nlinarith only [hp, hq, hr, hu]

end FourthRowPhiOmega2
end Wu2008DoubleSieve
