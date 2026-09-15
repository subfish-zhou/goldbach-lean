import MathlibNt.Wu2008DoubleSieve.SeventhEighthFixedGeometry
import MathlibNt.Wu2008DoubleSieve.NinthCoefficientClosure

/-! Actual fixed seventh/eighth switching, with every exception paid at the
same singular-series scale. No counting, packing, or payment input remains. -/
namespace Wu2008DoubleSieve.SeventhEighth
open Finset Real

/-- Combine the three actual exceptional atom counts. -/
theorem finite_switching_power {N : ℕ} {k : ℝ} {D : Finset (ℕ × ℕ)}
    (hN : 4 ≤ N) (he : Even N) (hk : 0 < k) (hkhi : k ≤ 1 / 2)
    (hD : PairDomain N k D) (hcut : 2 ≤ (N : ℝ) ^ k)
    (hg : ∀ t ∈ D, Nat.Prime t.1 ∧ Nat.Prime t.2 ∧ N ≤ t.1 * t.2 ^ 3) :
    ((∑ t ∈ D, sieveCount N (t.1 * t.2) (N * t.1) t.2 : ℤ) : ℝ) ≤
      ((physical N D).card : ℝ) + (5 / k ^ 2) * (N : ℝ) ^ (1 - k) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsqrt : sqrt N ≤ (N : ℝ) ^ (1 - k) := by
    rw [sqrt_eq_rpow]
    exact rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hone : 1 ≤ (N : ℝ) ^ (1 - k) := one_le_rpow hN1 (by linarith)
  have hb := divisorBad_bound hN he hk hD
  have hs := squareBad_bound hN he hk hD hcut
  have hu := unitBad_bound hN he hk hD
  have hsq := mul_le_mul_of_nonneg_left (add_le_add hsqrt hone)
    (by positivity : 0 ≤ 1 / k ^ 2)
  have hf := finite_switching hN he hg
  have hfR : ((∑ t ∈ D, sieveCount N (t.1 * t.2) (N * t.1) t.2 : ℤ) : ℝ) ≤
      ((physical N D).card : ℝ) + ((divisorBad N D).card : ℝ) +
        ((squareBad N D).card : ℝ) + ((unitBad N D).card : ℝ) := by
    exact_mod_cast hf
  calc
    _ ≤ ((physical N D).card : ℝ) + 1 / k ^ 2 *
        ((N : ℝ) ^ (1 - k) + (N : ℝ) ^ (1 - k)) +
        2 / k ^ 2 * (N : ℝ) ^ (1 - k) + 1 / k ^ 2 * (N : ℝ) ^ (1 - k) := by
      linarith
    _ = _ := by ring

theorem lowerS2_fixed_le_physicalT7 {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (hz : 2 ≤ z N) :
    (lowerS2 N (w N) (u N) : ℝ) ≤ ((physicalT7 N).card : ℝ) +
      (5 / alpha ^ 2) * (N : ℝ) ^ (1 - alpha) := by
  exact finite_switching_power hN he (by norm_num [alpha]) (by norm_num [alpha])
    (seventh_pairDomain (by omega)) hz (seventh_geometry (by omega))

theorem lowerS3_fixed_le_physicalT8 {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (hz : 2 ≤ z N) :
    (lowerS3 N (z N) (v N) : ℝ) ≤ ((physicalT8 N).card : ℝ) +
      (5 / alpha ^ 2) * (N : ℝ) ^ (1 - alpha) := by
  exact finite_switching_power hN he (by norm_num [alpha]) (by norm_num [alpha])
    (eighth_pairDomain N) hz (eighth_geometry (by omega))

/-- The original integer counts, with their unchanged weights 2 and 1. -/
theorem fixed_weighted_switching_power {N : ℕ} (hN : 4 ≤ N) (he : Even N)
    (hz : 2 ≤ z N) :
    ((2 * lowerS2 N (w N) (u N) + lowerS3 N (z N) (v N) : ℤ) : ℝ) ≤
      2 * ((physicalT7 N).card : ℝ) + ((physicalT8 N).card : ℝ) +
        (15 / alpha ^ 2) * (N : ℝ) ^ (1 - alpha) := by
  have h7 := lowerS2_fixed_le_physicalT7 hN he hz
  have h8 := lowerS3_fixed_le_physicalT8 hN he hz
  push_cast
  calc
    _ ≤ 2 * (((physicalT7 N).card : ℝ) +
        5 / alpha ^ 2 * (N : ℝ) ^ (1 - alpha)) +
        (((physicalT8 N).card : ℝ) + 5 / alpha ^ 2 * (N : ℝ) ^ (1 - alpha)) := by
      linarith
    _ = _ := by ring

/-- A genuine cutoff for N^alpha ≥ 2, not the insufficient N ≥ 512. -/
theorem exists_fixed_cutoff : ∃ T : ℕ, ∀ N : ℕ, T ≤ N → 2 ≤ z N := by
  obtain ⟨T, hT⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / alpha))
  refine ⟨T, ?_⟩
  intro N hN
  have hbound : (2 : ℝ) ^ (1 / alpha) ≤ N :=
    hT.trans (by exact_mod_cast hN)
  have hp := rpow_le_rpow (by positivity : 0 ≤ (2 : ℝ) ^ (1 / alpha)) hbound
    (by norm_num [alpha] : 0 ≤ alpha)
  have heq : ((2 : ℝ) ^ (1 / alpha)) ^ alpha = 2 := by
    rw [← rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num [alpha]
  rw [heq] at hp
  exact hp

/-- For each positive epsilon there is one threshold, chosen before N.
The physical carriers preserve the original pair domains and all r = b labels.
The unit, relative-sifted square, and p-divides-N exceptions have all been paid. -/
theorem fixed_weighted_switching_epsilon {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((2 * lowerS2 N (w N) (u N) + lowerS3 N (z N) (v N) : ℤ) : ℝ) ≤
        2 * ((physicalT7 N).card : ℝ) + ((physicalT8 N).card : ℝ) +
          ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
  have hC1 : 0 < wuSingularSeries 1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨Tcut, hcut⟩ := exists_fixed_cutoff
  obtain ⟨Tpay, hTpay, hpay⟩ := ninth_power_log_error_budget 0
    (by norm_num [alpha] : 0 < 15 / alpha ^ 2)
    (by norm_num [alpha] : 0 < alpha)
    (show 0 < ε * wuSingularSeries 1 by positivity)
  refine ⟨max Tcut Tpay, hTpay.trans (le_max_right _ _), ?_⟩
  intro N hN he
  have hNc := (le_max_left Tcut Tpay).trans hN
  have hNp := (le_max_right Tcut Tpay).trans hN
  have hN512 := hTpay.trans hNp
  have hpos : 0 < N := by omega
  have hf := fixed_weighted_switching_power (by omega : 4 ≤ N) he (hcut N hNc)
  have herr := hpay N hNp
  have heq : (15 / alpha ^ 2) * (N : ℝ) ^ (1 - alpha) =
      (15 / alpha ^ 2) * N * log N ^ (0 : ℕ) / (N : ℝ) ^ alpha := by
    rw [rpow_sub (by positivity : (0 : ℝ) < N), rpow_one, pow_zero]
    ring
  rw [← heq] at herr
  have hClow := wuSingularSeries_le_of_dvd (by norm_num : 0 < (1 : ℕ)) hpos (one_dvd N)
  have hCpay := mul_le_mul_of_nonneg_left hClow
    (show 0 ≤ ε * N / log N ^ (2 : ℕ) by positivity)
  have hpaid : ε * wuSingularSeries 1 * N / log N ^ (2 : ℕ) ≤
      ε * wuSingularSeries N * N / log N ^ (2 : ℕ) := by
    calc
      _ = (ε * N / log N ^ (2 : ℕ)) * wuSingularSeries 1 := by ring
      _ ≤ (ε * N / log N ^ (2 : ℕ)) * wuSingularSeries N := hCpay
      _ = _ := by ring
  linarith

end Wu2008DoubleSieve.SeventhEighth
