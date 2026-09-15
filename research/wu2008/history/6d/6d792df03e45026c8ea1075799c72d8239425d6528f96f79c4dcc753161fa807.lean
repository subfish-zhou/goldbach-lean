import MathlibNt.Wu2008DoubleSieve.TruncatedSixthLowerAP

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

noncomputable def truncatedSixthLowerPairs (N : ℕ) (δ : ℝ) : Finset (ℕ × ℕ) :=
  (truncatedSixthPairs N ((N : ℝ) ^ truncatedSixthLowerAlpha)
    ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)).filter
      (fun t => (t.1 : ℝ) * t.2 ≤
        (N : ℝ) ^ (truncatedSixthLowerC δ - 2 * truncatedSixthLowerAlpha))

noncomputable def truncatedSixthLowerPrimeS (N : ℕ) (δ : ℝ) (t : ℕ × ℕ) : ℝ :=
  log ((N : ℝ) ^ (truncatedSixthLowerC δ) / (t.1 * t.2 : ℕ)) /
    log ((N : ℝ) ^ truncatedSixthLowerAlpha)

theorem truncatedSixthLower_coordinate_window {N p : ℕ} {a b : ℝ}
    (hN : 1 < N) (hp : p ∈ primeWindow N ((N : ℝ) ^ a) ((N : ℝ) ^ b)) :
    a ≤ log (p : ℝ) / log N ∧ log (p : ℝ) / log N < b := by
  obtain ⟨hp, _, hlo, hhi⟩ := mem_primeWindow.mp hp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  constructor
  · apply (le_div_iff₀ hlog).mpr
    simpa only [log_rpow hN0, mul_comm] using log_le_log (rpow_pos_of_pos hN0 _) hlo
  · apply (div_lt_iff₀ hlog).mpr
    simpa only [log_rpow hN0, mul_comm] using log_lt_log hp0 hhi

theorem truncatedSixthLower_prime_region {N : ℕ} {δ : ℝ} {t : ℕ × ℕ}
    (hN : 1 < N) (ht : t ∈ truncatedSixthLowerPairs N δ) :
    truncatedSixthLowerRegion δ (log (t.1 : ℝ) / log N) (log (t.2 : ℝ) / log N) := by
  obtain ⟨ht, hprod⟩ := mem_filter.mp ht
  obtain ⟨hp, hq⟩ := mem_product.mp ht
  have hpwin := truncatedSixthLower_coordinate_window hN hp
  have hqwin := truncatedSixthLower_coordinate_window hN hq
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have hp0 : (0 : ℝ) < t.1 := by exact_mod_cast (mem_primeWindow.mp hp).1.pos
  have hq0 : (0 : ℝ) < t.2 := by exact_mod_cast (mem_primeWindow.mp hq).1.pos
  refine ⟨hpwin.1, hpwin.2.le, hqwin.1, hqwin.2.le, ?_⟩
  have h := log_le_log (mul_pos hp0 hq0) hprod
  rw [log_mul hp0.ne' hq0.ne', log_rpow hN0] at h
  rw [← add_div]
  exact (div_le_iff₀ hlog).mpr h

theorem truncatedSixthLower_prime_s_eq {N : ℕ} {δ : ℝ} {t : ℕ × ℕ}
    (hN : 1 < N) (ht : t ∈ truncatedSixthLowerPairs N δ) :
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

theorem truncatedSixthLower_pairs_subset {N : ℕ} {δ : ℝ}
    (hN : 1 < N) (hδ : 0 < δ) :
    truncatedSixthLowerPairs N δ ⊆
      truncatedSixthKept N ((N : ℝ) ^ truncatedSixthLowerAlpha)
        ((N : ℝ) ^ truncatedSixthLowerBeta) ((N : ℝ) ^ truncatedSixthLowerSigma)
        ((N : ℝ) ^ truncatedSixthLowerLambda) := by
  intro t ht
  obtain ⟨ht, hprod⟩ := mem_filter.mp ht
  refine mem_filter.mpr ⟨ht, hprod.trans_lt ?_⟩
  apply rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hN)
  unfold truncatedSixthLowerC truncatedSixthLowerLambda
  linarith

theorem truncatedSixthLower_prime_s_bounds {N : ℕ} {δ : ℝ} {t : ℕ × ℕ}
    (hN : 1 < N) (hδ : 0 ≤ δ) (ht : t ∈ truncatedSixthLowerPairs N δ) :
    2 ≤ truncatedSixthLowerPrimeS N δ t ∧ truncatedSixthLowerPrimeS N δ t ≤ 5 := by
  rw [truncatedSixthLower_prime_s_eq hN ht]
  exact (truncatedSixthLower_region_bounds hδ (truncatedSixthLower_prime_region hN ht)).2.2.2

end Wu2008DoubleSieve
