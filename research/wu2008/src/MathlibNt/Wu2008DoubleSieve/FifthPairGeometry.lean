import MathlibNt.Wu2008DoubleSieve.BaseLowerAssembly
import MathlibNt.Wu2008DoubleSieve.ElevenTermAssembly

namespace Wu2008DoubleSieve
open Finset Real Filter
open scoped Classical Topology

/-- Literal ordered labels; no product image and no symmetry divisor. -/
noncomputable def fifthPairLabels (N : ℕ) : Finset (ℕ × ℕ) :=
  ((primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha)
    ((N : ℝ) ^ truncatedSixthLowerBeta)) ×ˢ
   (primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha)
    ((N : ℝ) ^ truncatedSixthLowerBeta))).filter (fun t => t.1 < t.2)

noncomputable def fifthPairCount (N : ℕ) : ℤ :=
  ∑ q ∈ primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha)
    ((N : ℝ) ^ truncatedSixthLowerBeta),
    ∑ p ∈ primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha) (q : ℝ),
      sieveCount N (p * q) N ((N : ℝ) ^ truncatedSixthLowerAlpha)

/-- Entire original triangle, with its original canonical lower coefficient. -/
noncomputable def fifthPairFdelta (δ : ℝ) : ℝ :=
  4 * ∫ y in truncatedSixthLowerAlpha..truncatedSixthLowerBeta,
    ∫ x in truncatedSixthLowerAlpha..y,
      wuLowerCoefficient (truncatedSixthLowerS δ x y) /
        (x * y * (truncatedSixthLowerC δ - x - y))

noncomputable def fifthPairFlin : ℝ := fifthPairFdelta 0

theorem fifthPair_sum_eq (N : ℕ) (f : ℕ × ℕ → ℝ) :
    (∑ t ∈ fifthPairLabels N, f t) =
    ∑ q ∈ primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha)
      ((N : ℝ) ^ truncatedSixthLowerBeta),
      ∑ p ∈ primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha) (q : ℝ), f (p,q) := by
  unfold fifthPairLabels
  rw [sum_filter, sum_product, sum_comm]
  apply sum_congr rfl
  intro q hq
  have hwin : (primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha)
      ((N : ℝ) ^ truncatedSixthLowerBeta)).filter (fun p => p < q) =
      primeWindow N ((N : ℝ) ^ truncatedSixthLowerAlpha) (q : ℝ) := by
    ext p
    simp only [mem_filter, mem_primeWindow]
    constructor
    · rintro ⟨⟨hp, hc, hlo, _⟩, hpq⟩
      exact ⟨hp, hc, hlo, by exact_mod_cast hpq⟩
    · rintro ⟨hp, hc, hlo, hpq⟩
      exact ⟨⟨hp, hc, hlo, hpq.trans (mem_primeWindow.mp hq).2.2.2⟩,
        by exact_mod_cast hpq⟩
  rw [← hwin, sum_filter]

theorem fifthPair_count_eq (N : ℕ) :
    (fifthPairCount N : ℝ) = ∑ t ∈ fifthPairLabels N,
      (sieveCount N (t.1 * t.2) N ((N : ℝ) ^ truncatedSixthLowerAlpha) : ℝ) := by
  rw [fifthPair_sum_eq]
  simp only [fifthPairCount, Int.cast_sum]

theorem fifthPair_triangle_bounds {δ x y : ℝ}
    (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000)
    (hx : truncatedSixthLowerAlpha ≤ x) (hxy : x ≤ y)
    (hy : y ≤ truncatedSixthLowerBeta) :
    0 < x ∧ 0 < y ∧ 2 ≤ truncatedSixthLowerS δ x y ∧
      truncatedSixthLowerS δ x y ≤ 5 ∧
      x + 2 * y ≤ 3 * truncatedSixthLowerBeta ∧
      3 * truncatedSixthLowerBeta < truncatedSixthLowerC δ := by
  have hα := truncatedSixthLower_parameters.1
  refine ⟨hα.trans_le hx, hα.trans_le (hx.trans hxy), ?_, ?_, by linarith, ?_⟩
  · apply (le_div_iff₀ hα).mpr
    norm_num [truncatedSixthLowerC, truncatedSixthLowerAlpha, truncatedSixthLowerBeta] at *
    linarith
  · apply (div_le_iff₀ hα).mpr
    norm_num [truncatedSixthLowerC, truncatedSixthLowerAlpha, truncatedSixthLowerBeta] at *
    linarith
  · norm_num [truncatedSixthLowerC, truncatedSixthLowerBeta] at *
    linarith

theorem fifthPair_prime_s_eq {N : ℕ} {δ : ℝ} {t : ℕ × ℕ}
    (hN : 1 < N) (ht : t ∈ fifthPairLabels N) :
    truncatedSixthLowerPrimeS N δ t =
      truncatedSixthLowerS δ (log (t.1 : ℝ) / log N) (log (t.2 : ℝ) / log N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  obtain ⟨hp, hq⟩ := mem_product.mp (mem_filter.mp ht).1
  have hp0 : (0 : ℝ) < t.1 := by exact_mod_cast (mem_primeWindow.mp hp).1.pos
  have hq0 : (0 : ℝ) < t.2 := by exact_mod_cast (mem_primeWindow.mp hq).1.pos
  unfold truncatedSixthLowerPrimeS truncatedSixthLowerS
  rw [Nat.cast_mul, log_div (rpow_pos_of_pos hN0 _).ne' (mul_pos hp0 hq0).ne',
    log_mul hp0.ne' hq0.ne', log_rpow hN0, log_rpow hN0]
  field_simp
  ring

theorem fifthPair_prime_s_bounds {N : ℕ} {δ : ℝ} {t : ℕ × ℕ}
    (hN : 1 < N) (hδ : 0 ≤ δ) (hδhi : δ ≤ 1 / 1000)
    (ht : t ∈ fifthPairLabels N) :
    2 ≤ truncatedSixthLowerPrimeS N δ t ∧ truncatedSixthLowerPrimeS N δ t ≤ 5 := by
  rw [fifthPair_prime_s_eq hN ht]
  obtain ⟨hwin, hpq⟩ := mem_filter.mp ht
  obtain ⟨hp, hq⟩ := mem_product.mp hwin
  have hx := truncatedSixthLower_coordinate_window hN hp
  have hy := truncatedSixthLower_coordinate_window hN hq
  have hp0 : (0 : ℝ) < t.1 := by exact_mod_cast (mem_primeWindow.mp hp).1.pos
  have hxy : log (t.1 : ℝ) / log N ≤ log (t.2 : ℝ) / log N :=
    div_le_div_of_nonneg_right (log_le_log hp0 (by exact_mod_cast hpq.le))
      (log_nonneg (by exact_mod_cast hN.le))
  have h := fifthPair_triangle_bounds hδ hδhi hx.1 hxy hy.2.le
  exact ⟨h.2.2.1, h.2.2.2.1⟩

/-- Inner ordered rectangles retain their literal finite prime labels. -/
theorem fifthPair_cell_subset {N : ℕ} {a b c d : ℝ}
    (hN : 1 < N) (ha : truncatedSixthLowerAlpha ≤ a)
    (hbc : b ≤ c) (hd : d ≤ truncatedSixthLowerBeta) :
    truncatedSixthClosurePairs N a b c d ⊆ fifthPairLabels N := by
  intro t ht
  obtain ⟨hp, hq⟩ := mem_product.mp ht
  have hp' := mem_primeWindow.mp hp
  have hq' := mem_primeWindow.mp hq
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  have hpq : (t.1 : ℝ) < t.2 := hp'.2.2.2.trans_le
    ((rpow_le_rpow_of_exponent_le hNR hbc).trans hq'.2.2.1)
  have hpβ := hpq.trans (hq'.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hNR hd))
  have hαp := (rpow_le_rpow_of_exponent_le hNR ha).trans hp'.2.2.1
  exact mem_filter.mpr ⟨mem_product.mpr
    ⟨mem_primeWindow.mpr ⟨hp'.1, hp'.2.1, hαp, hpβ⟩,
     mem_primeWindow.mpr ⟨hq'.1, hq'.2.1, hαp.trans hpq.le,
       hq'.2.2.2.trans_le (rpow_le_rpow_of_exponent_le hNR hd)⟩⟩,
    by exact_mod_cast hpq⟩

end Wu2008DoubleSieve
