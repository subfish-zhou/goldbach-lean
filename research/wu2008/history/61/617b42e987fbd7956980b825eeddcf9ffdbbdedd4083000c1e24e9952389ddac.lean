import MathlibNt.Wu2008DoubleSieve.TruncatedSixthLowerGain

/-!
# Sign-safe local-product normalization on the whole retained polygon

The generic polynomial-envelope theorem is applied to the actual N,
not to an assumed source box. The coefficient loss is theta-weighted,
so it remains valid near s = 2 where the perturbed density is negative.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

noncomputable def truncatedSixthLowerClassicalTheta (N : ℕ) (δ : ℝ)
    (t : ℕ × ℕ) : ℝ :=
  4 * logarithmicIntegral N * wuSingularSeries N /
    ((Nat.totient (t.1 * t.2) : ℝ) *
      log ((N : ℝ) ^ truncatedSixthLowerC δ / (t.1 * t.2 : ℕ)))

noncomputable def truncatedSixthLowerNormalizedMain (N : ℕ) (δ η : ℝ)
    (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ t ∈ S, (wuLowerCoefficient (truncatedSixthLowerPrimeS N δ t) - 15 * η) *
    truncatedSixthLowerClassicalTheta N δ t

theorem truncatedSixthLower_local_relative {η : ℝ} (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, Even N →
      |localSieveProduct N ((N : ℝ) ^ truncatedSixthLowerAlpha) /
        (2 * exp (-eulerMascheroniConstant) * wuSingularSeries N /
          log ((N : ℝ) ^ truncatedSixthLowerAlpha)) - 1| ≤ η := by
  have hα := truncatedSixthLower_parameters.1
  have hlocal := eventually_localSieveProduct_relative (1 / truncatedSixthLowerAlpha) η
    (by positivity) hη
  have ht := ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually hlocal
  filter_upwards [ht, eventually_ge_atTop (1 : ℕ)] with N hN hN1 he
  have hN0 : (0 : ℝ) ≤ N := by positivity
  apply hN N (by omega) he
  change (N : ℝ) ≤ ((N : ℝ) ^ truncatedSixthLowerAlpha) ^ (1 / truncatedSixthLowerAlpha)
  rw [← rpow_mul hN0, mul_one_div_cancel hα.ne', rpow_one]

theorem truncatedSixthLower_normalized_main_le {δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η) (hηhi : η ≤ 1) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ S : Finset (ℕ × ℕ), S ⊆ truncatedSixthLowerPairs N δ →
      truncatedSixthLowerNormalizedMain N δ η S ≤
        truncatedSixthLowerClassicalMain N δ (exp eulerMascheroniConstant * η / 2) S := by
  filter_upwards [truncatedSixthLower_local_relative hη,
    eventually_ge_atTop (4 : ℕ)] with N hlocal hN he S hS
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hα := truncatedSixthLower_parameters.1
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogz : 0 < log ((N : ℝ) ^ truncatedSixthLowerAlpha) := by
    rw [log_rpow hNR]
    positivity
  unfold truncatedSixthLowerNormalizedMain truncatedSixthLowerClassicalMain
  apply sum_le_sum
  intro t ht
  have hs := truncatedSixthLower_prime_s_bounds (by omega) hδ (hS ht)
  let s := truncatedSixthLowerPrimeS N δ t
  let l := log ((N : ℝ) ^ truncatedSixthLowerC δ / (t.1 * t.2 : ℕ))
  have hsl : s * log ((N : ℝ) ^ truncatedSixthLowerAlpha) = l :=
    div_mul_cancel₀ _ hlogz.ne'
  have hl : 0 < l := by
    rw [← hsl]
    exact mul_pos (by dsimp [s]; linarith [hs.1]) hlogz
  have hM : 2 * s * wuSingularSeries N / (exp eulerMascheroniConstant * l) =
      2 * exp (-eulerMascheroniConstant) * wuSingularSeries N /
        log ((N : ℝ) ^ truncatedSixthLowerAlpha) := by
    rw [exp_neg]
    dsimp [s, truncatedSixthLowerPrimeS]
    change 2 * (l / log ((N : ℝ) ^ truncatedSixthLowerAlpha)) * wuSingularSeries N /
      (exp eulerMascheroniConstant * l) = _
    field_simp
  have hV := hlocal he
  rw [← hM] at hV
  have hbudget := canonical_lower_bounded_normalization_budget hs.1
    (by linarith [hs.2]) (wuSingularSeries_pos N hN0) hl hη.le hηhi hV
  have hX : 0 ≤ logarithmicIntegral N / (Nat.totient (t.1 * t.2) : ℝ) :=
    div_nonneg (MathlibNt.SieveTheory.LiuWeight.liuLogarithmicIntegral_nonneg 0
      le_rfl (by exact_mod_cast (show 2 ≤ N by omega))) (Nat.cast_nonneg _)
  have h := mul_le_mul_of_nonneg_left hbudget hX
  change (logarithmicIntegral N / (Nat.totient (t.1 * t.2) : ℝ)) *
    ((wuLowerCoefficient s - 15 * η) * (4 * wuSingularSeries N / l)) ≤ _ at h
  calc
    _ = (logarithmicIntegral N / (Nat.totient (t.1 * t.2) : ℝ)) *
        ((wuLowerCoefficient s - 15 * η) * (4 * wuSingularSeries N / l)) := by
      dsimp [s, l, truncatedSixthLowerClassicalTheta]
      ring
    _ ≤ _ := h

theorem truncatedSixthLower_normalized_masked {δ η A : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hηhi : η ≤ 1) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ S : Finset (ℕ × ℕ), S ⊆ truncatedSixthLowerPairs N δ →
        truncatedSixthLowerNormalizedMain N δ η S - C * (N : ℝ) / log N ^ A ≤
          ∑ t ∈ S, (sieveCount N (t.1 * t.2) N
            ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨C, hC, T, hT4, hT⟩ := truncatedSixthLower_classical_masked hδ
    (show 0 < exp eulerMascheroniConstant * η / 2 by positivity) hA
  obtain ⟨T1, hT1⟩ := eventually_atTop.mp
    (truncatedSixthLower_normalized_main_le hδ.le hη hηhi)
  refine ⟨C, hC, max T T1, hT4.trans (le_max_left _ _), ?_⟩
  intro N hN he S hS
  exact (sub_le_sub_right (hT1 N ((le_max_right _ _).trans hN) he S hS) _).trans
    (hT N ((le_max_left _ _).trans hN) he S hS)

theorem truncatedSixthLower_normalized_actual_mass {δ η A : ℝ}
    (hδ : 0 < δ) (hη : 0 < η) (hηhi : η ≤ 1) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthLowerNormalizedMain N δ η (truncatedSixthLowerPairs N δ) -
        C * (N : ℝ) / log N ^ A ≤
      (truncatedSixthMass N ((N : ℝ) ^ truncatedSixthLowerAlpha)
        ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
        ((N : ℝ) ^ truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨C, hC, T, hT, h⟩ := truncatedSixthLower_normalized_masked hδ hη hηhi hA
  refine ⟨C, hC, T, hT, ?_⟩
  intro N hN he
  apply (h N hN he _ subset_rfl).trans
  unfold truncatedSixthMass
  push_cast
  apply sum_le_sum_of_subset_of_nonneg (truncatedSixthLower_pairs_subset (by omega) hδ)
  intro t _ _
  exact_mod_cast (show (0 : ℤ) ≤ sieveCount N (t.1 * t.2) N
    ((N : ℝ) ^ truncatedSixthLowerAlpha) from Int.natCast_nonneg _)

end Wu2008DoubleSieve
