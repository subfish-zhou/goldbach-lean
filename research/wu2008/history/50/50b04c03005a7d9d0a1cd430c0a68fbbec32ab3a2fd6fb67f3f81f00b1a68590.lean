import MathlibNt.Wu2008DoubleSieve.TruncatedSixthLowerNormalization
import MathlibNt.Wu2008DoubleSieve.Omega3XNormalization

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

theorem truncatedSixthLower_AP_relative {C ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / log N ^ (3 : ℕ) ≤
        ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  have hC1 := wuSingularSeries_pos 1 (by norm_num)
  have hgrowth := (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (C / (ε * wuSingularSeries 1)))
  filter_upwards [hgrowth, eventually_ge_atTop (4 : ℕ)] with N hg hN
  change C / (ε * wuSingularSeries 1) ≤ log (N : ℝ) at hg
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC := wuSingularSeries_le_of_dvd (by norm_num : 0 < (1 : ℕ))
    hN0 (one_dvd N)
  have hpay : C / log (N : ℝ) ≤ ε * wuSingularSeries 1 := by
    apply (div_le_iff₀ hlog).mpr
    have h := (div_le_iff₀ (mul_pos hε hC1)).mp hg
    linarith
  calc
    _ = (C / log (N : ℝ)) * (N / log N ^ (2 : ℕ)) := by ring
    _ ≤ (ε * wuSingularSeries 1) * (N / log N ^ (2 : ℕ)) :=
      mul_le_mul_of_nonneg_right hpay (by positivity)
    _ ≤ (ε * wuSingularSeries N) * (N / log N ^ (2 : ℕ)) := by gcongr
    _ = _ := by ring

theorem truncatedSixthLower_normalized_masked_relative {δ η ε : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ S : Finset (ℕ × ℕ), S ⊆ truncatedSixthLowerPairs N δ →
        truncatedSixthLowerNormalizedMain N δ η S -
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
          ∑ t ∈ S, (sieveCount N (t.1 * t.2) N
            ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨C, _, T, hT4, hT⟩ := truncatedSixthLower_normalized_masked
    hδ hη hηhi (by norm_num : (0 : ℝ) < 3)
  obtain ⟨T1, hT1⟩ := eventually_atTop.mp (truncatedSixthLower_AP_relative (C := C) hε)
  refine ⟨max T T1, hT4.trans (le_max_left _ _), ?_⟩
  intro N hN he S hS
  have h := hT N ((le_max_left _ _).trans hN) he S hS
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, rpow_natCast] at h
  exact (sub_le_sub_left (hT1 N ((le_max_right _ _).trans hN)) _).trans h

theorem truncatedSixthLower_mask_mass_le {N : ℕ} {δ : ℝ}
    (hN : 1 < N) (hδ : 0 < δ) (S : Finset (ℕ × ℕ))
    (hS : S ⊆ truncatedSixthLowerPairs N δ) :
    (∑ t ∈ S, (sieveCount N (t.1 * t.2) N
      ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ)) ≤
      (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
        ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
        ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  unfold truncatedSixthMass
  push_cast
  apply sum_le_sum_of_subset_of_nonneg (hS.trans (truncatedSixthLower_pairs_subset hN hδ))
  intro t _ _
  exact_mod_cast (show (0 : ℤ) ≤ sieveCount N (t.1 * t.2) N
    ((N : ℝ) ^ truncatedSixthLowerAlpha) from Int.natCast_nonneg _)

theorem truncatedSixthLower_normalized_actual_relative {δ η ε : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthLowerNormalizedMain N δ η (truncatedSixthLowerPairs N δ) -
        ε * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
      (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
        ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
        ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨T, hT, h⟩ := truncatedSixthLower_normalized_masked_relative hδ hη hηhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he
  exact (h N hN he _ subset_rfl).trans
    (truncatedSixthLower_mask_mass_le (by omega) hδ _ subset_rfl)

end Wu2008DoubleSieve
