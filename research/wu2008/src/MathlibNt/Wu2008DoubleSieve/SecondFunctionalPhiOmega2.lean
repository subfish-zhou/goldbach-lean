import MathlibNt.Wu2008DoubleSieve.SecondFunctionalParameters
import MathlibNt.Wu2008DoubleSieve.FourthRowPhiOmega2

/-! # Shared actual Phi/Omega2 block with three independent negative windows
The five real count estimates share epsilon/8. All gamma credits remain
outside this block, and delta is fixed throughout. -/
namespace Wu2008DoubleSieve
namespace SecondFunctionalPhiOmega2
open FourthRowPhiOmega2 SecondFunctionalParameters

/-- No finite count, mass, integrability, or limiting inequality is a premise. -/
theorem actual_limit_block (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    (hs : 2 ≤ p.s) (hS : 3 ≤ p.S) (hS5 : p.S ≤ 5)
    (k : ℕ) (hk : 1 ≤ k) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        4 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.S +
          wuBoxPhi N δ (convolutionWuWindows N Δ V) p.kappa1 -
          wuOmega2Sum N δ p.s p.S (convolutionWuWindows N Δ V) -
          wuOmega2Sum N δ p.kappa2 p.S (convolutionWuWindows N Δ V) -
          wuOmega2Sum N δ p.kappa3 p.S (convolutionWuWindows N Δ V) ≤
        (4 * wuUpperCoefficient p.S + wuUpperCoefficient p.kappa1 -
          4 * wuImprovementLimit true δ p.S - wuImprovementLimit true δ p.kappa1 -
          J δ p.s p.S - J δ p.kappa2 p.S - J δ p.kappa3 p.S + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hs3 := hp.s_le_kappa3
  have h32 := hp.kappa3_lt_kappa2.le
  have h21 := hp.kappa2_lt_kappa1.le
  have h1S := hp.kappa1_le_S
  have hδhalf : δ < 1 / 2 := by linarith
  have heps : 0 < ε / 8 := by positivity
  obtain ⟨P, hP4, hP⟩ := phi_actual_limit_upper k hk hδ hδhalf
    (show 1 ≤ p.S by linarith) hp.S_le_ten heps
  obtain ⟨Q, _, hQ⟩ := phi_actual_limit_upper k hk hδ hδhalf
    (show 1 ≤ p.kappa1 by linarith) (h1S.trans hp.S_le_ten) heps
  obtain ⟨R, _, hR⟩ := omega2_actual_limit_lower k hk hδ hδhi
    hs (hs3.trans (h32.trans (h21.trans h1S))) hS hS5 heps
  obtain ⟨U, _, hU⟩ := omega2_actual_limit_lower k hk hδ hδhi
    (hs.trans (hs3.trans h32)) (h21.trans h1S) hS hS5 heps
  obtain ⟨Z, _, hZ⟩ := omega2_actual_limit_lower k hk hδ hδhi
    (hs.trans hs3) (h32.trans (h21.trans h1S)) hS hS5 heps
  let T := max (max P Q) (max (max R U) Z)
  have hPT : P ≤ T := (le_max_left _ _).trans (le_max_left _ _)
  have hQT : Q ≤ T := (le_max_right _ _).trans (le_max_left _ _)
  have hRT : R ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hUT : U ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hZT : Z ≤ T := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨T, hP4.trans hPT, ?_⟩
  intro N hN he i Δ V hb
  have hpN := hP N (hPT.trans hN) he i Δ V hb
  have hqN := hQ N (hQT.trans hN) he i Δ V hb
  have hrN := hR N (hRT.trans hN) he i Δ V hb
  have huN := hU N (hUT.trans hN) he i Δ V hb
  have hzN := hZ N (hZT.trans hN) he i Δ V hb
  nlinarith only [hpN, hqN, hrN, huN, hzN]

/-- The four original records satisfy the additional analytic domain bounds. -/
theorem four_rows_analytic (p : SecondFunctionalParameters)
    (hp : p = row1 ∨ p = row2 ∨ p = row3 ∨ p = row4) :
    p.MotherAdmissible ∧ 2 ≤ p.s ∧ 3 ≤ p.S ∧ p.S ≤ 5 := by
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨row1_motherAdmissible, by norm_num [row1], by norm_num [row1], by norm_num [row1]⟩
  · exact ⟨row2_motherAdmissible, by norm_num [row2], by norm_num [row2], by norm_num [row2]⟩
  · exact ⟨row3_motherAdmissible, by norm_num [row3], by norm_num [row3], by norm_num [row3]⟩
  · exact ⟨row4_motherAdmissible, by norm_num [row4], by norm_num [row4], by norm_num [row4]⟩

end SecondFunctionalPhiOmega2
end Wu2008DoubleSieve
