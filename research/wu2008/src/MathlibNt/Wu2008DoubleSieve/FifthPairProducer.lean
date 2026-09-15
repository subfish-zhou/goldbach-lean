import MathlibNt.Wu2008DoubleSieve.FifthPairGeometry

/-! Actual full ordered-triangle Rosser producer, with coprime masks,
strict cutoff, uniform AP payment, and sign-safe singular-series normalization.
No target count estimate is a hypothesis. -/
namespace Wu2008DoubleSieve
open Finset Real Filter
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

theorem fifthPair_classical_masked {δ ρ A : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hρ : 0 < ρ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ S : Finset (ℕ × ℕ), S ⊆ fifthPairLabels N →
        truncatedSixthLowerClassicalMain N δ ρ S - C * (N : ℝ) / log N ^ A ≤
          ∑ t ∈ S, (sieveCount N (t.1 * t.2) N
            ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨z0, hlower⟩ := truncatedSixthLower_pair_signed hρ
  obtain ⟨C, hC, T1, hAP⟩ :=
    truncatedSixthLower_masked_AP_uniform truncatedSixthLower_parameters.1 hδ hA
  have hz := ((tendsto_rpow_atTop truncatedSixthLower_parameters.1).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (max z0 2))
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp hz
  refine ⟨C, hC, max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N hN he S hS
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : 1 < N := by omega
  have hNT1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNT2 : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hz0 := (le_max_left z0 2).trans (hT2 N hNT2)
  have hz2 := (le_max_right z0 2).trans (hT2 N hNT2)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrect : S ⊆ primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha)
      ((N : ℝ) ^ truncatedSixthLowerBeta) ×ˢ
      primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha)
        ((N : ℝ) ^ truncatedSixthLowerBeta) :=
    fun t ht => (mem_filter.mp (hS ht)).1
  have herr := hAP N hNT1 _ _
    (fun p hp => let h := mem_primeWindow.mp hp; ⟨h.1, h.2.1, h.2.2.1⟩)
    (fun q hq => let h := mem_primeWindow.mp hq; ⟨h.1, h.2.1, h.2.2.1⟩)
    S hrect ((N : ℝ) ^ truncatedSixthLowerAlpha)
  have hpoint : ∀ t ∈ S,
      (logarithmicIntegral N / (Nat.totient (t.1 * t.2) : ℝ)) *
        ((jr1965f (truncatedSixthLowerPrimeS N δ t) - ρ) *
          localSieveProduct N ((N : ℝ) ^ truncatedSixthLowerAlpha)) ≤
      (sieveCount N (t.1 * t.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) +
        |ordinaryRosserRemainder false N (t.1 * t.2)
          (⌊(N : ℝ) ^ (1 / 2 - δ) / (t.1 * t.2 : ℕ)⌋₊ + 1)
          ((N : ℝ) ^ truncatedSixthLowerAlpha)| := by
    intro t ht
    obtain ⟨hp, hq⟩ := mem_product.mp (hrect ht)
    have hp' := mem_primeWindow.mp hp
    have hq' := mem_primeWindow.mp hq
    have hprod : (0 : ℝ) < (t.1 * t.2 : ℕ) := by
      exact_mod_cast mul_pos hp'.1.pos hq'.1.pos
    have hs := fifthPair_prime_s_bounds hN1 hδ.le hδhi (hS ht)
    have h := hlower N t.1 t.2 he (by omega) hp'.1 hq'.1
      ((N : ℝ) ^ truncatedSixthLowerAlpha)
      ((N : ℝ) ^ truncatedSixthLowerC δ / (t.1 * t.2 : ℕ))
      (truncatedSixthLowerPrimeS N δ t) hp'.2.2.1 hq'.2.2.1
      hz0 hz2 (div_pos (rpow_pos_of_pos hN0 _) hprod) rfl hs.1 (by linarith [hs.2])
    have hr := neg_abs_le (ordinaryRosserRemainder false N (t.1 * t.2)
      (⌊(N : ℝ) ^ (1 / 2 - δ) / (t.1 * t.2 : ℕ)⌋₊ + 1)
      ((N : ℝ) ^ truncatedSixthLowerAlpha))
    change _ + ordinaryRosserRemainder false N (t.1 * t.2)
      (⌊(N : ℝ) ^ (1 / 2 - δ) / (t.1 * t.2 : ℕ)⌋₊ + 1)
      ((N : ℝ) ^ truncatedSixthLowerAlpha) ≤ _ at h
    linarith
  have hsum := sum_le_sum hpoint
  rw [sum_add_distrib] at hsum
  unfold truncatedSixthLowerClassicalMain
  linarith

theorem fifthPair_normalized_main_le {δ η : ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000) (hη : 0 < η) (hηhi : η ≤ 1) :
    ∀ᶠ N : ℕ in atTop, Even N →
      ∀ S : Finset (ℕ × ℕ), S ⊆ fifthPairLabels N →
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
  have hs := fifthPair_prime_s_bounds (by omega) hδ hδhi (hS ht)
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

theorem fifthPair_normalized_masked {δ η A : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hη : 0 < η) (hηhi : η ≤ 1) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ S : Finset (ℕ × ℕ), S ⊆ fifthPairLabels N →
        truncatedSixthLowerNormalizedMain N δ η S - C * (N : ℝ) / log N ^ A ≤
          ∑ t ∈ S, (sieveCount N (t.1 * t.2) N
            ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨C, hC, T, hT4, hT⟩ := fifthPair_classical_masked hδ hδhi
    (show 0 < exp eulerMascheroniConstant * η / 2 by positivity) hA
  obtain ⟨T1, hT1⟩ := eventually_atTop.mp
    (fifthPair_normalized_main_le hδ.le hδhi hη hηhi)
  refine ⟨C, hC, max T T1, hT4.trans (le_max_left _ _), ?_⟩
  intro N hN he S hS
  exact (sub_le_sub_right (hT1 N ((le_max_right _ _).trans hN) he S hS) _).trans
    (hT N ((le_max_left _ _).trans hN) he S hS)

theorem fifthPair_normalized_masked_relative {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ S : Finset (ℕ × ℕ), S ⊆ fifthPairLabels N →
        truncatedSixthLowerNormalizedMain N δ η S -
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤
          ∑ t ∈ S, (sieveCount N (t.1 * t.2) N
            ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  obtain ⟨C, _, T, hT4, hT⟩ := fifthPair_normalized_masked
    hδ hδhi hη hηhi (by norm_num : (0 : ℝ) < 3)
  obtain ⟨T1, hT1⟩ := eventually_atTop.mp (truncatedSixthLower_AP_relative (C := C) hε)
  refine ⟨max T T1, hT4.trans (le_max_left _ _), ?_⟩
  intro N hN he S hS
  have h := hT N ((le_max_left _ _).trans hN) he S hS
  rw [show (3 : ℝ) = (3 : ℕ) by norm_num, rpow_natCast] at h
  exact (sub_le_sub_left (hT1 N ((le_max_right _ _).trans hN)) _).trans h

theorem fifthPair_normalized_actual_relative {δ η ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 1000) (hη : 0 < η) (hηhi : η ≤ 1) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthLowerNormalizedMain N δ η (fifthPairLabels N) -
        ε * wuSingularSeries N * N / log N ^ (2 : ℕ) ≤ (fifthPairCount N : ℝ) := by
  obtain ⟨T, hT, h⟩ := fifthPair_normalized_masked_relative hδ hδhi hη hηhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he
  rw [fifthPair_count_eq]
  exact h N hN he _ subset_rfl

end Wu2008DoubleSieve
