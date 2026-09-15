import SrcSingleAnalyticOmegaIntegral

noncomputable section
namespace WuSource.SrcSingle.Analytic
open Wu2008DoubleSieve Real Finset
open scoped Classical BigOperators
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

def coupledLinear (row : SecondFunctionalParameters) : ℝ :=
  4 * wuUpperCoefficient row.S + wuUpperCoefficient row.kappa1 -
    fourthRowClassicalJ row.s row.S - fourthRowClassicalJ row.kappa2 row.S -
    fourthRowClassicalJ row.kappa3 row.S

def coupledGamma (j : Fin 3) (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 5 21, secondFunctionalMotherGammaSum (Wu04RemainingCore.row j) N δ
    (fun _ : Fin 1 => psiPrimes (j.castAdd 4) N) k

def gammaAllowance (j : Fin 3) (δ : ℝ) : ℝ :=
  SecondFunctionalCoupledFeedback.classical (Wu04RemainingCore.row j) +
    2 * ActualNineFeedback.coupledCostMass (Wu04RemainingCore.row j) / (1 - 2 * δ)

theorem coupled_row_ranges (j : Fin 3) :
    psiNode (j.castAdd 4) ≤ (Wu04RemainingCore.row j).S ∧
    psiNode (j.castAdd 4) ≤ (Wu04RemainingCore.row j).kappa1 ∧
    (Wu04RemainingCore.row j).kappa1 ≤ psiTop (j.castAdd 4) ∧
    psiNode (j.castAdd 4) ≤ (Wu04RemainingCore.row j).kappa2 ∧
    (Wu04RemainingCore.row j).kappa2 ≤ psiTop (j.castAdd 4) ∧
    psiNode (j.castAdd 4) ≤ (Wu04RemainingCore.row j).kappa3 ∧
    (Wu04RemainingCore.row j).kappa3 ≤ psiTop (j.castAdd 4) := by
  have hp := (ActualNineFeedback.coupledRow_geometry j.succ).1.mother
  change (Wu04RemainingCore.row j).MotherAdmissible at hp
  rw [(seven_source_rows.1 j).1, (seven_source_rows.1 j).2]
  have h31 := hp.kappa3_lt_kappa2.le.trans hp.kappa2_lt_kappa1.le
  exact ⟨hp.s_le_kappa3.trans (h31.trans hp.kappa1_le_S),
    hp.s_le_kappa3.trans h31, hp.kappa1_le_S,
    hp.s_le_kappa3.trans hp.kappa3_lt_kappa2.le,
    hp.kappa2_lt_kappa1.le.trans hp.kappa1_le_S,
    hp.s_le_kappa3, h31.trans hp.kappa1_le_S⟩

theorem coupled_RHS_analytic_prefix (j : Fin 3) {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      secondFunctionalMotherRHS (Wu04RemainingCore.row j) N δ
        (fun _ : Fin 1 => psiPrimes (j.castAdd 4) N) ≤
      coupledLinear (Wu04RemainingCore.row j) * theta (j.castAdd 4) N δ +
        coupledGamma j N δ + ε * truncatedSixthMassScale N := by
  have hr := coupled_row_ranges j
  have hs := (seven_source_rows.1 j).1
  have hS := (seven_source_rows.1 j).2
  have he : 0 < ε / 8 := by positivity
  obtain ⟨TP, hTP4, hTP⟩ := phi_upper_paid hd hh he
  obtain ⟨T1, _, hT1⟩ := omega2_integral_paid
    (j := j.castAdd 4) (a := (Wu04RemainingCore.row j).s) hs.le
    (by rw [← hs, ← hS]; exact (seven_parameter_geometry (j.castAdd 4)).2.2.2.2.1) hd hh he
  obtain ⟨T2, _, hT2⟩ := omega2_integral_paid hr.2.2.2.1 hr.2.2.2.2.1 hd hh he
  obtain ⟨T3, _, hT3⟩ := omega2_integral_paid hr.2.2.2.2.2.1 hr.2.2.2.2.2.2 hd hh he
  refine ⟨max TP (max T1 (max T2 T3)), hTP4.trans (le_max_left _ _), fun N hN hev => ?_⟩
  have hphiS := hTP N (by omega) hev (j.castAdd 4) _ hr.1 hS.symm.le
  have hphi1 := hTP N (by omega) hev (j.castAdd 4) _ hr.2.1 hr.2.2.1
  have ho1 := hT1 N (by omega) hev
  have ho2 := hT2 N (by omega) hev
  have ho3 := hT3 N (by omega) hev
  simp only [J, hS] at ho1 ho2 ho3
  unfold coupledLinear secondFunctionalMotherRHS coupledGamma
  unfold fourthRowClassicalJ
  linarith only [hphiS, hphi1, ho1, ho2, ho3]

theorem coupled_allowance_identity (j : Fin 3) {δ : ℝ} (hh : δ ≤ 1 / 100) :
    coupledLinear (Wu04RemainingCore.row j) + gammaAllowance j δ =
      5 * (1 - coupledForcing δ j) := by
  have hg := ActualNineFeedback.coupledRow_geometry j.succ
  change ActualNineFeedback.CoupledGeometry (Wu04RemainingCore.row j) at hg
  have hbase := Wu08OriginalPsiRecovery.coupledBase_eq_original_logs hg
  have hA : wuUpperCoefficient (Wu04RemainingCore.row j).s = 1 := by
    rw [wuUpperCoefficient, jr1965F_eq_of_le_three hg.1.s_le_three]
    have hs : (Wu04RemainingCore.row j).s ≠ 0 := by linarith [hg.1.two_lt_s]
    field_simp
  unfold ActualNineFeedback.coupledBase at hbase
  rw [hA] at hbase
  unfold coupledLinear gammaAllowance coupledForcing
  have hden : 1 - 2 * δ ≠ 0 := by linarith
  field_simp [hden]
  nlinarith only [hbase]

theorem coupled_actual_count_with_Gamma_remainder (j : Fin 3) {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      5 * psiCount (j.castAdd 4) N ≤
        5 * (1 - coupledForcing δ j) * theta (j.castAdd 4) N δ +
          (coupledGamma j N δ - gammaAllowance j δ * theta (j.castAdd 4) N δ) +
          ε * truncatedSixthMassScale N := by
  obtain ⟨T, hT4, hT⟩ := coupled_RHS_analytic_prefix j hd hh heps
  refine ⟨T, hT4, fun N hN he => ?_⟩
  have h := (coupled_high_actual_finite j (by omega : 2 ≤ N) hd hh).trans (hT N hN he)
  rw [← coupled_allowance_identity j hh]
  nlinarith only [h]

#check @coupled_RHS_analytic_prefix
#check @coupled_actual_count_with_Gamma_remainder
#print axioms coupled_RHS_analytic_prefix
#print axioms coupled_actual_count_with_Gamma_remainder
end WuSource.SrcSingle.Analytic
