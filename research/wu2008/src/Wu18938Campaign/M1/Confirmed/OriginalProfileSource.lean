import Wu18938Campaign.M1.Confirmed.ProfileSourceIdentity
import Wu18938Campaign.M1.Confirmed.ProfileGainOrder

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FiniteProfile

open Wu2008DoubleSieve Rebox Real NodeExtension ActualNineFeedback
open scoped Classical

theorem originalProfile_abs_bound (δ : ℝ) (n : ℕ) (v : ℝ) :
    |originalProfile δ n v| ≤ 1 := by
  rw [abs_of_nonneg (originalProfile_bounds δ n v).1]
  exact (originalProfile_bounds δ n v).2.trans (by norm_num)

theorem originalProfile_second_source {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (n : ℕ) (j : Fin 4) (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      let H := originalProfile δ n
      let p := coupledRow j
      wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
        (1 - (coupledBase p - deltaLoss δ * coupledLoss p +
          (4 * eProfile H p.S + eProfile H p.kappa1 +
            lowerGainJ H p.s p.S + lowerGainJ H p.kappa2 p.S + lowerGainJ H p.kappa3 p.S +
            feedbackDensityMoment p H) / 5) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hh := second_gain_actual (coupledRow j) (coupledRow_geometry j).1
    (originalProfile_antitone δ n) (fun v _ => originalProfile_bounds δ n v)
    hδ hδhi (originalProfile_actual hδ hδhi n) m hη he
  rw [second_gain_source_identity (originalProfile_antitone δ n)
    (originalProfile_abs_bound δ n) (coupledRow j) (coupledRow_geometry j) δ (by linarith)] at hh
  exact hh

theorem originalProfile_first_source {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (n : ℕ) (j : Fin 5) (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      let H := originalProfile δ n
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (firstNode j) ≤
        (1 - (firstFunctionalGainPsi δ (firstNode j) (firstS j) +
          eProfile H (firstS j) + lowerGainJ H (firstNode j) (firstS j) / 2) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hg := first_geometry j
  have hs : 2 < firstNode j := by
    dsimp [firstNode]
    have hh := Nat.cast_nonneg (α := ℝ) j.val
    linarith
  have hh := first_gain_actual (originalProfile_antitone δ n)
    (fun v _ => originalProfile_bounds δ n v) hδ hδhi hg.1 (hg.2.1.trans hg.2.2.1)
    hg.2.2.1 hg.2.2.2.1 (originalProfile_actual hδ hδhi n) m hη he
  rw [first_gain_source_identity (originalProfile_antitone δ n) hs hg.2.1
    hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2] at hh
  exact hh

end Wu18938Campaign.M1.Confirmed.FiniteProfile
