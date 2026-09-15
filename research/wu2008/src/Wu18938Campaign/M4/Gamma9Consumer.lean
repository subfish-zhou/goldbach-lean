import Wu18938Campaign.M4.Gamma9Upper
import WR2PsiCostsSuprema

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh WuSource.SrcSingle
open WuPaper.R2PsiCosts Finset Real
open scoped Classical

private theorem gamma9_parameters (j : Fin 3) :
    0 ≤ I9 (Wu04RemainingCore.row j) ∧ I9 (Wu04RemainingCore.row j) ≤ 10000 := by
  rw [I9_eq]
  have hp := (row_analytic j).mother
  exact omega3XIntegralEnvelope_uniform_cap
    ((row_analytic j).two_lt_s.le.trans hp.s_le_kappa3)
    (hp.kappa3_lt_kappa2.le.trans hp.kappa2_lt_kappa1.le)
    (hp.kappa1_le_S.trans hp.S_le_ten)

private theorem gamma9_coefficient_radius {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      ∀ j : Fin 3,
      (2 / (1 - 2 * δ)) * I9 (Wu04RemainingCore.row j) *
        (8 * psiLogWeight (j.castAdd 4)) ≤
      16 * psiLogWeight (j.castAdd 4) * I9 (Wu04RemainingCore.row j) + ε := by
  let f := fun (j : Fin 3) (δ : ℝ) =>
    (2 / (1 - 2 * δ)) * I9 (Wu04RemainingCore.row j) *
      (8 * psiLogWeight (j.castAdd 4))
  have hc (j : Fin 3) : ContinuousAt (f j) 0 := by
    dsimp only [f]
    fun_prop (disch := norm_num)
  choose r hr hb using fun j => Metric.continuousAt_iff.mp (hc j) ε heps
  let R := min (1 / 100 : ℝ) (min (r 0) (min (r 1) (r 2)))
  have hR : 0 < R := lt_min (by norm_num) (lt_min (hr 0) (lt_min (hr 1) (hr 2)))
  have hRj (j : Fin 3) : R ≤ r j := by
    have h0 : R ≤ r 0 := (min_le_right _ _).trans (min_le_left _ _)
    have h12 : R ≤ min (r 1) (r 2) := (min_le_right _ _).trans (min_le_right _ _)
    fin_cases j
    · exact h0
    · exact h12.trans (min_le_left _ _)
    · exact h12.trans (min_le_right _ _)
  refine ⟨R, hR, min_le_left _ _, ?_⟩
  intro δ hd hdr j
  have hdist : dist δ (0 : ℝ) < r j := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hd]
    exact hdr.trans_le (hRj j)
  have h := (abs_lt.mp (show |f j δ - f j 0| < ε by
    simpa only [Real.dist_eq] using hb j hdist)).2
  have hzero : f j 0 =
      16 * psiLogWeight (j.castAdd 4) * I9 (Wu04RemainingCore.row j) := by
    dsimp only [f]
    ring
  rw [hzero] at h
  change f j δ ≤ _
  linarith only [h]

theorem gamma9_original_small_delta {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      gamma j N δ 9 ≤
        (16 * psiLogWeight (j.castAdd 4) * I9 (Wu04RemainingCore.row j) + ε) *
          truncatedSixthMassScale N := by
  let η := ε / 60002
  have heta : 0 < η := by dsimp only [η]; positivity
  obtain ⟨r0, hr0, hr0hi, T0, hT04, hnorm⟩ := theta_original_error heta
  obtain ⟨r1, hr1, _, hc⟩ := gamma9_coefficient_radius (half_pos heps)
  refine ⟨min r0 r1, lt_min hr0 hr1, (min_le_left _ _).trans hr0hi, ?_⟩
  intro δ hd hdr
  have hd0 := hdr.trans_le (min_le_left r0 r1)
  have hd1 := hdr.trans_le (min_le_right r0 r1)
  have hh : δ ≤ 1 / 100 := hd0.le.trans hr0hi
  obtain ⟨T1, _, hactual⟩ := gamma9_upper_fixed hd hh heta
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN he j
  have hN4 : 4 ≤ N := by omega
  have hM := truncatedSixthClosure_scale_nonneg hN4
  let B := (2 / (1 - 2 * δ)) * I9 (Wu04RemainingCore.row j)
  have hB0 : 0 ≤ B := mul_nonneg
    (div_nonneg (by norm_num) (by linarith)) (gamma9_parameters j).1
  have hBcap : B ≤ 30000 := by
    have hD : 2 / (1 - 2 * δ) ≤ (3 : ℝ) :=
      (div_le_iff₀ (by linarith)).mpr (by linarith)
    have h := mul_le_mul hD (gamma9_parameters j).2
      (gamma9_parameters j).1 (by norm_num : (0 : ℝ) ≤ 3)
    calc
      B ≤ 3 * 10000 := h
      _ = 30000 := by norm_num
  have ht := (abs_le.mp (hnorm δ hd hd0 N (by omega) he j)).2
  have hb := mul_le_mul_of_nonneg_left ht hB0
  have hpay := mul_le_mul_of_nonneg_right hBcap (mul_nonneg heta.le hM)
  have hcoef := mul_le_mul_of_nonneg_right (hc δ hd hd1 j) hM
  have ha := hactual N (by omega) he j
  rw [← I9_eq] at ha
  change gamma j N δ 9 ≤ B * theta j N δ + η * truncatedSixthMassScale N at ha
  change B * (8 * psiLogWeight (j.castAdd 4)) * truncatedSixthMassScale N ≤ _ at hcoef
  dsimp only [η] at ha hb hpay
  nlinarith only [ha, hb, hpay, hcoef]

def unpaidTwelve (j : Fin 3) (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ i ∈ Icc 10 21, gamma j N δ i

theorem unpaidThirteen_split (j : Fin 3) (N : ℕ) (δ : ℝ) :
    unpaidThirteen j N δ = gamma j N δ 9 + unpaidTwelve j N δ := by
  norm_num [unpaidThirteen, unpaidTwelve, Finset.sum_Icc_succ_top]
  ring

theorem actual_count_twelve_pending {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3,
      psiCount (j.castAdd 4) N ≤
        (8 * psiLogWeight (j.castAdd 4) *
          (1 - classicalGain j + (2 / 5) * I9 (Wu04RemainingCore.row j)) + ε) *
            truncatedSixthMassScale N + unpaidTwelve j N δ / 5 := by
  obtain ⟨r0, hr0, hr0hi, h0⟩ := actual_count_partial_original (half_pos heps)
  obtain ⟨r1, hr1, _, h1⟩ := gamma9_original_small_delta
    (show 0 < 5 * ε / 2 by positivity)
  refine ⟨min r0 r1, lt_min hr0 hr1, (min_le_left _ _).trans hr0hi, ?_⟩
  intro δ hd hdr
  obtain ⟨T0, hT04, hc⟩ := h0 δ hd (hdr.trans_le (min_le_left _ _))
  obtain ⟨T1, _, hg⟩ := h1 δ hd (hdr.trans_le (min_le_right _ _))
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN he j
  have hc' := hc N (by omega) he j
  have hg' := hg N (by omega) he j
  rw [unpaidThirteen_split] at hc'
  nlinarith only [hc', hg']

end Wu18938Campaign.M4
