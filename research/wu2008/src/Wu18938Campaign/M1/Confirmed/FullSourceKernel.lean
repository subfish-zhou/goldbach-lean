import Wu18938Campaign.M1.Confirmed.PairOriginalIntegrals
import Wu18938Campaign.M1.Confirmed.FullProfileIteration
import Wu18938Campaign.M1.Confirmed.ProfileSourceIdentity
import WR2MatrixOriginalSystem

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.FullProfile

open Wu2008DoubleSieve Real MeasureTheory NodeExtension ActualNineFeedback FiniteProfile
open scoped Classical Interval

theorem original_xi2_eq (p : SecondFunctionalParameters) (v : ℝ) :
    WuPaper.R2Xi.Xi2 p v = WuPaper.R2Matrix.xi2 v p := by
  rw [WuPaper.R2Matrix.xi2_literal]
  rfl

theorem second_gain_original_kernel {H : ℝ → ℝ} (hH : Antitone H)
    (hHb : ∀ v, |H v| ≤ 1) (j : Fin 4) (δ : ℝ) (hδ : δ < 1 / 2) :
    secondGain (coupledRow j) δ H =
      coupledBase (coupledRow j) - deltaLoss δ * coupledLoss (coupledRow j) +
        ∫ v in (1 : ℝ)..3, H v * WuPaper.R2Matrix.sourceKernel ⟨j.val,by omega⟩ v := by
  have hp := coupledRow_geometry j
  have hg := coupled_geometry_bounds hp
  have hJ0 := lower_profile_J_split hH hp.1.two_lt_s hg.2.1 hp.1.three_le_S hp.1.S_le_five hp.2.2.1
  have hJ2 := lower_profile_J_split hH
    (hp.1.two_lt_s.trans_le (hp.1.mother.s_le_kappa3.trans hp.1.mother.kappa3_lt_kappa2.le))
    hg.2.2.2.1 hp.1.three_le_S hp.1.S_le_five hp.2.2.2.1
  have hJ3 := lower_profile_J_split hH (hp.1.two_lt_s.trans_le hp.1.mother.s_le_kappa3)
    hg.2.2.2.2.2.1 hp.1.three_le_S hp.1.S_le_five hp.2.2.2.2
  have hG := PairLiteral.four_original_integrals hp.1 hH.measurable hHb
  have hxi := WuPaper.R2Xi.original_four_rows_integral_identity H
    (hH.intervalIntegrable (μ := volume)) j
  have hk (v : ℝ) :
      WuPaper.R2Matrix.sourceKernel ⟨j.val,by omega⟩ v = WuPaper.R2Xi.Xi2 (coupledRow j) v := by
    simp only [WuPaper.R2Matrix.sourceKernel,j.isLt,↓reduceDIte,original_xi2_eq]
  simp_rw [hk]
  rw [hxi]
  have ha : wuUpperCoefficient (coupledRow j).s = 1 :=
    jr1965F_normalized_initial (by linarith [hp.1.two_lt_s]) hp.1.s_le_three
  unfold secondGain coefficient
  rw [upper_profile_E hH hp.1.three_le_S hp.1.S_le_five,
    upper_profile_E hH hp.2.1 hg.2.2.2.2.2.2,hJ0,hJ2,hJ3,
    Finset.sum_sub_distrib,classical_pair_sum,hG]
  unfold coupledBase coupledCostMass deltaLoss coupledLoss
  unfold coupledCostMass
  rw [ha]
  change _ = _ + (lowerGainJ H (coupledRow j).s (coupledRow j).S +
    lowerGainJ H (coupledRow j).kappa2 (coupledRow j).S +
    lowerGainJ H (coupledRow j).kappa3 (coupledRow j).S +
    4 * eProfile H (coupledRow j).S + eProfile H (coupledRow j).kappa1 +
    WuPaper.R2Xi.original66 H (coupledRow j) + WuPaper.R2Xi.original67 H (coupledRow j) +
    WuPaper.R2Xi.original68 H (coupledRow j)) / 5
  have hd : 1 - 2 * δ ≠ 0 := by linarith
  field_simp
  ring

theorem profile_abs_bound (δ : ℝ) (n : ℕ) (v : ℝ) :
    |untruncatedProfile δ n v| ≤ 1 := by
  rw [abs_of_nonneg (profile_bounds δ n v).1]
  exact (profile_bounds δ n v).2.trans (by norm_num)

theorem profile_original_second {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1 / 100)
    (n : ℕ) (j : Fin 4) (m : ℕ) {η ε : ℝ} (hη : 0 < η) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      wuBoxPhi N δ (convolutionWuWindows N Δ V) (coupledRow j).s ≤
        (1 - (coupledBase (coupledRow j) - deltaLoss δ * coupledLoss (coupledRow j) +
          ∫ v in (1 : ℝ)..3,
            untruncatedProfile δ n v * WuPaper.R2Matrix.sourceKernel ⟨j.val,by omega⟩ v) + ε) *
          boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  have hh := second_gain_actual j (profile_antitone δ n) (fun v _ => profile_bounds δ n v)
    hδ hδhi (profile_actual hδ hδhi n) m hη he
  rw [second_gain_original_kernel (profile_antitone δ n) (profile_abs_bound δ n)
    j δ (by linarith)] at hh
  exact hh

end Wu18938Campaign.M1.Confirmed.FullProfile
