import MathlibNt.SieveTheory.LiLiuGoldbachG10CorrectedIntegralUpper
import MathlibNt.SieveTheory.LiLiuGoldbachWeightLogScale
import MathlibNt.SieveTheory.LiLiuGoldbachWeightTwelve

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem WeightI10Consumer_beta_lt_switch :
    goldbachB10Beta < (1 - 3 * goldbachB10Beta) / 3 := by
  norm_num [goldbachB10Beta]

private theorem WeightI10Consumer_switch_lt_gamma :
    (1 - 3 * goldbachB10Beta) / 3 < goldbachB10Gamma := by
  norm_num [goldbachB10Beta, goldbachB10Gamma]

private theorem WeightI10Consumer_gamma_lt_third :
    goldbachB10Gamma < (1 : ℝ) / 3 := by
  norm_num [goldbachB10Gamma]

/-- Consume the proved `I10` upper bound into the actual signed eleven-term
base expression, keeping the literal `goldbachWeightTwelveBase` rather than
asserting any separate positivity of that base. -/
theorem goldbachWeight_twelve_base_I10_consumed_eventually
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε : ℝ, 0 < ε → ε < (2 : ℝ) / 15 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N → ∀ α : ℝ,
        (1 : ℝ) / 18 < α → α < goldbachB10Beta →
          (goldbachWeightTwelveBase (goldbachDifferenceCarrier N ε) N
            ((N : ℝ) ^ α) ((N : ℝ) ^ goldbachB10Beta)
            ((N : ℝ) ^ goldbachB10Gamma) ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) : ℝ) -
            (8 * (1 - ε) * goldbachB10I10 + δ) *
              (SingularSeries.liuSingularSeries N * (N : ℝ) /
                Real.log (N : ℝ) ^ 2) ≤
            4 * (D19 N : ℝ) := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hδU : 0 < (δ / 2) * SingularSeries.liuUniversalProduct := by
    exact mul_pos hδ2 SingularSeries.liuUniversalProduct_pos
  obtain ⟨Ne, hNe2, he⟩ := goldbach_power_error_le_log_scale_eventually
    1334 ((1 : ℝ) / 18) ((δ / 2) * SingularSeries.liuUniversalProduct)
    (by norm_num) (by norm_num) hδU
  intro ε hε hεu
  have hε1 : ε < 1 := by linarith
  obtain ⟨Nc, hc⟩ := goldbachWeight_twelve_corrected_lower_bound_eventually ε hε hεu
  obtain ⟨Ng, hNg4, hg⟩ := goldbachG10Corrected_I10_upper (δ / 2) hδ2 ε hε hε1
  refine ⟨max 4 (max Nc (max Ng Ne)), le_max_left _ _, ?_⟩
  intro N hN hEven α hα hαβ
  let A : Finset ℕ := goldbachDifferenceCarrier N ε
  let S : ℝ :=
    SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2
  have hNrest : max Nc (max Ng Ne) ≤ N := (le_max_right _ _).trans hN
  have hNc : Nc ≤ N := (le_max_left _ _).trans hNrest
  have hNrest' : max Ng Ne ≤ N := (le_max_right _ _).trans hNrest
  have hNg : Ng ≤ N := (le_max_left _ _).trans hNrest'
  have hNe : Ne ≤ N := (le_max_right _ _).trans hNrest'
  have hmain :=
    hc N hNc hEven α goldbachB10Beta goldbachB10Gamma hα hαβ
      WeightI10Consumer_beta_lt_switch WeightI10Consumer_switch_lt_gamma
      WeightI10Consumer_gamma_lt_third
  have hG :
      (goldbachG10Corrected A N
        ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma) : ℝ) ≤
        (8 * (1 - ε) * goldbachB10I10 + δ / 2) * S := by
    simpa [A, S, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hg N hNg hEven
  have hraw :
      1334 * (N : ℝ) ^ (1 - α) ≤
        ((δ / 2) * SingularSeries.liuUniversalProduct) *
          ((N : ℝ) / Real.log (N : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      he N hNe α hα.le
  have hpaySeries :
      ((δ / 2) * SingularSeries.liuUniversalProduct) *
          ((N : ℝ) / Real.log (N : ℝ) ^ 2) ≤
        (δ / 2) * S := by
    have hseries :
        (δ / 2) * SingularSeries.liuUniversalProduct ≤
          (δ / 2) * SingularSeries.liuSingularSeries N := by
      exact mul_le_mul_of_nonneg_left
        (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hδ2.le
    have hLnonneg : 0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ 2 := by
      positivity
    simpa [S, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_right hseries hLnonneg)
  have hpay : 1334 * (N : ℝ) ^ (1 - α) ≤ (δ / 2) * S := hraw.trans hpaySeries
  have hconsume :
      (goldbachG10Corrected A N
        ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma) : ℝ) +
        1334 * (N : ℝ) ^ (1 - α) ≤
          (8 * (1 - ε) * goldbachB10I10 + δ) * S := by
    calc
      _ ≤ (8 * (1 - ε) * goldbachB10I10 + δ / 2) * S + (δ / 2) * S :=
        add_le_add hG hpay
      _ = _ := by ring
  have hmain' :
      (goldbachWeightTwelveBase A N
        ((N : ℝ) ^ α) ((N : ℝ) ^ goldbachB10Beta)
        ((N : ℝ) ^ goldbachB10Gamma) ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) : ℝ) -
        ((goldbachG10Corrected A N
          ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma) : ℝ) +
          1334 * (N : ℝ) ^ (1 - α)) ≤
          4 * (D19 N : ℝ) := by
    dsimp only [goldbachWeightTwelveCorrectedRHS, A] at hmain
    push_cast at hmain
    linarith
  have hgoal :
      (goldbachWeightTwelveBase A N
        ((N : ℝ) ^ α) ((N : ℝ) ^ goldbachB10Beta)
        ((N : ℝ) ^ goldbachB10Gamma) ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) : ℝ) -
          (8 * (1 - ε) * goldbachB10I10 + δ) * S ≤
        4 * (D19 N : ℝ) := by
    calc
      (goldbachWeightTwelveBase A N
        ((N : ℝ) ^ α) ((N : ℝ) ^ goldbachB10Beta)
        ((N : ℝ) ^ goldbachB10Gamma) ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) : ℝ) -
          (8 * (1 - ε) * goldbachB10I10 + δ) * S
          ≤
          (goldbachWeightTwelveBase A N
            ((N : ℝ) ^ α) ((N : ℝ) ^ goldbachB10Beta)
            ((N : ℝ) ^ goldbachB10Gamma) ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) : ℝ) -
            ((goldbachG10Corrected A N
              ((N : ℝ) ^ goldbachB10Beta) ((N : ℝ) ^ goldbachB10Gamma) : ℝ) +
              1334 * (N : ℝ) ^ (1 - α)) := by
                linarith
      _ ≤ 4 * (D19 N : ℝ) := hmain'
  simpa [A, S] using hgoal

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig