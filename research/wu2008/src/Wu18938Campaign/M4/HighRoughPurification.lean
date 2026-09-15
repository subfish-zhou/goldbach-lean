import Wu18938Campaign.M4.HighRestrictedDensity
import Wu18938Campaign.M4.HighUnitNegligible
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughPurification

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh HighNonunit Finset Real Filter
open scoped Classical

theorem original_nonunit_square_paid {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3, ∀ high : Bool,
      (originalNonunitFamily j N δ high).squareRawMass ((N : ℝ) ^ (1 / 40 : ℝ)) ≤
        ε * truncatedSixthMassScale N := by
  obtain ⟨T0, hT04, hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 1 heps
    (show (0 : ℝ) < 4 * 40 ^ 6 by positivity) (show (0 : ℝ) < 1 / 40 by norm_num)
  obtain ⟨T1, hpow⟩ := eventually_atTop.mp
    (box_eventually_log_power_budget 0 (show (0 : ℝ) < 2 by norm_num)
      (show (0 : ℝ) < 1 / 40 by norm_num))
  obtain ⟨T2, hlog⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ)))
  refine ⟨max T0 (max T1 T2), hT04.trans (le_max_left _ _), ?_⟩
  intro δ hd hh N hN j high
  let Y := (N : ℝ) ^ (1 / 40 : ℝ)
  have hY : 2 ≤ Y := by simpa only [pow_zero, mul_one] using hpow N (by omega)
  have hY0 : 0 < Y := by linarith
  have hYm : 0 < Y - 1 := by linarith
  have hlog1 := hlog N (by omega)
  dsimp only [Function.comp_apply] at hlog1
  have hlog0 : 0 ≤ log (N : ℝ) := by linarith
  have hs := (originalNonunitFamily j N δ high).squareRawMass_le hY
    (by positivity : (0 : ℝ) ≤ 40 ^ 6)
    (original_nonunit_family_fibre j (by omega) hd hh high)
  have hinv : 1 / (Y - 1) ≤ 2 / Y := by
    apply (div_le_div_iff₀ hYm hY0).mpr
    linarith
  calc
    _ ≤ (40 : ℝ) ^ 6 * N * (1 + log N) / (Y - 1) := hs
    _ = ((40 : ℝ) ^ 6 * N * (1 + log N)) * (1 / (Y - 1)) := by ring
    _ ≤ ((40 : ℝ) ^ 6 * N * (1 + log N)) * (2 / Y) :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ ((40 : ℝ) ^ 6 * N * (2 * log N)) * (2 / Y) := by
      gcongr
      linarith
    _ = (4 * (40 : ℝ) ^ 6) * N * log N ^ 1 / (N : ℝ) ^ (1 / 40 : ℝ) := by
      dsimp only [Y]
      ring
    _ ≤ _ := hp N (by omega)

theorem original_high_gamma_rough_density {δ ρ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hrho : 0 < ρ) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ high : Bool,
      gamma j N δ (if high then 21 else 20) ≤
        ((originalNonunitFamily j N δ high).restrictLabels profileRough).mass *
          (HighO3.densityFactor δ ρ * wuSingularSeries N / log N) +
            ε * truncatedSixthMassScale N := by
  have he : 0 < ε / 4 := by positivity
  obtain ⟨T0, hT04, hden⟩ := original_restricted_prime_density hd hh hrho he
  obtain ⟨T1, _, hunit⟩ := original_unit_word_paid he
  obtain ⟨T2, _, hsquare⟩ := original_nonunit_square_paid he
  obtain ⟨T3, _, hbad⟩ := original_nonunit_bad_paid hd hh he
  refine ⟨max T0 (max T1 (max T2 T3)), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven j high
  let L := originalNonunitFamily j N δ high
  have hf := original_high_gamma_le_unit_primeMass (δ := δ) j (by omega) hEven high
  have hpur := L.primeMass_le_restrict_add_square_add_bad profileRough
    ((N : ℝ) ^ (1 / 40 : ℝ)) (by
      intro x hx hc hn
      have hprof := (mem_filter.mp hx).1
      obtain ⟨_, _, _, _, hs, _⟩ := profile_data hprof
      exact masked_good_nonrough_square hs hc hn
        (original_nonunit_relative j (by omega) hd hh high hprof))
  have hu := hunit δ hd hh N (by omega) j (HighNonunit.word high)
    (by cases high <;> simp [HighNonunit.word, HighUnitSource.word20, HighUnitSource.word21])
  change actualUnit N δ (Wu04RemainingCore.row j) (windows j N) high ≤
    (ε / 4) * truncatedSixthMassScale N at hu
  have hs := hsquare δ hd hh N (by omega) j high
  have hb := hbad N (by omega) j high
  have hm := hden N (by omega) hEven j high profileRough
  nlinarith only [hf, hpur, hu, hs, hb, hm]

end Wu18938Campaign.M4
