import MathlibNt.Wu2008DoubleSieve.TruncatedElevenClassicalLower

/-! The complete classical coefficient is transferred to the actual finite
prime-complement count. The sixth term remains truncated in the producer.
The power error and the cutoff admission are proved on a common tail.
No positivity of the coefficient or stronger factor-size condition is asserted. -/
namespace Wu2008DoubleSieve.TruncatedElevenClassicalCountLower

open Finset Real Filter SingleUpperCounts SingleUpperClassicalLimit
open scoped Classical Topology

/-- The literal coefficient of the accepted complete truncated classical bound. -/
noncomputable def classicalCoefficient : ℝ :=
  24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
    8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
    truncatedSixthLowerF6lin + 47/481250 -
    Glin (1/3) - Glin truncatedSixthLowerSigma - 8*J9 -
    16*SeventhEighth.J7 - 8*SeventhEighth.J8 -
    8*FourRoughClosedMass.I10 - 8*FourRoughClosedMass.I11

/-- Admission to the actual finite counting inequality is not a public premise. -/
theorem fixed_cutoff_eventually_admissible :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      2 ≤ (N : ℝ) ^ (100 / 1327 : ℝ) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 100 / 1327)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2 : ℝ)))
  exact ⟨max T 512, le_max_right _ _, fun N hN =>
    hT N ((le_max_left _ _).trans hN)⟩

/-- Pay the actual positive-power exceptional budget in singular-series units. -/
theorem exceptional_power_error_paid {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      truncatedSixthErrorConstant * (N : ℝ) ^ (1 - (100 / 1327 : ℝ)) ≤
        ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  have hc : 0 < wuSingularSeries 1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨T, hT, hpay⟩ := ninth_power_log_error_budget 0
    truncatedSixthErrorConstant_pos (by norm_num : (0 : ℝ) < 100 / 1327)
    (show 0 < ε * wuSingularSeries 1 by positivity)
  refine ⟨T, hT, ?_⟩
  intro N hN
  have hNp : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNp
  have hClow := wuSingularSeries_le_of_dvd (by norm_num : 0 < (1 : ℕ))
    hNp (one_dvd N)
  have hscale := mul_le_mul_of_nonneg_left hClow
    (show 0 ≤ ε * N / log N ^ (2 : ℕ) by positivity)
  calc
    _ = truncatedSixthErrorConstant * N * log N ^ (0 : ℕ) /
        (N : ℝ) ^ (100 / 1327 : ℝ) := by
      rw [rpow_sub hNR, rpow_one, pow_zero]
      ring
    _ ≤ (ε * wuSingularSeries 1) * N / log N ^ (2 : ℕ) := hpay N hN
    _ = (ε * N / log N ^ (2 : ℕ)) * wuSingularSeries 1 := by ring
    _ ≤ (ε * N / log N ^ (2 : ℕ)) * wuSingularSeries N := hscale
    _ = _ := by ring

/-- Epsilon is the sole analytic premise; one threshold admits every even N. -/
theorem actual_count_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (classicalCoefficient - ε) * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨T1, hT1, hmain⟩ :=
    TruncatedElevenClassicalLower.truncated_fixed_classical_lower (half_pos hε)
  obtain ⟨T2, _, herror⟩ := exceptional_power_error_paid (half_pos hε)
  obtain ⟨T3, _, hcutoff⟩ := fixed_cutoff_eventually_admissible
  refine ⟨max T1 (max T2 T3), hT1.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hN1 : T1 ≤ N := (le_max_left _ _).trans hN
  have hN23 : max T2 T3 ≤ N := (le_max_right _ _).trans hN
  have hN2 : T2 ≤ N := (le_max_left _ _).trans hN23
  have hN3 : T3 ≤ N := (le_max_right _ _).trans hN23
  have hm := hmain N hN1 he
  change (classicalCoefficient - ε / 2) * wuSingularSeries N * N /
    log N ^ (2 : ℕ) ≤ (truncatedSixthFixedExpression N : ℝ) at hm
  have hp := herror N hN2
  have hf := truncatedSixth_fixed_le_count (by omega : 4 ≤ N) he (hcutoff N hN3)
  ring_nf at hm hp ⊢
  linarith only [hm, hp, hf]

/-- Expanded headline: every classical negative integral retains its exact weight. -/
theorem actual_count_lower_full_coefficient {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (24*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) +
        8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta)) + fifthPairFlin +
        truncatedSixthLowerF6lin + 47/481250 -
        Glin (1/3) - Glin truncatedSixthLowerSigma - 8*J9 -
        16*SeventhEighth.J7 - 8*SeventhEighth.J8 -
        8*FourRoughClosedMass.I10 - 8*FourRoughClosedMass.I11 - ε) *
          wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
        4 * ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) :=
  actual_count_lower hε

/-- The equivalent lower bound for the cardinality itself, with the same tail. -/
theorem actual_count_lower_div_four {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (classicalCoefficient - ε) * wuSingularSeries N * N /
        (4 * log N ^ (2 : ℕ)) ≤
          ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨T, hT, hcount⟩ := actual_count_lower hε
  refine ⟨T, hT, ?_⟩
  intro N hN he
  have h := hcount N hN he
  have hid : (classicalCoefficient - ε) * wuSingularSeries N * N /
      (4 * log N ^ (2 : ℕ)) =
      ((classicalCoefficient - ε) * wuSingularSeries N * N / log N ^ (2 : ℕ)) / 4 := by
    ring
  rw [hid]
  exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).2 (by linarith only [h])

end Wu2008DoubleSieve.TruncatedElevenClassicalCountLower
