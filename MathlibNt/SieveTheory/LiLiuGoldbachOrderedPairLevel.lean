import MathlibNt.SieveTheory.LiLiuGoldbachS3Carrier
import MathlibNt.SieveTheory.LiuPanPrimitiveLedgerAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem OrderedPairLevel_eventually_real_bound (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧
      2 * (N : ℝ) ^ (821 / 1749 : ℝ) ≤
        (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B := by
  have hlog := LiuWeight.eventually_pan_log_rpow_le_rpow B (107 / 6996) (by norm_num)
  have hconst : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (107 / 6996 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 107 / 6996)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  filter_upwards [eventually_ge_atTop (4 : ℕ), hlog, hconst] with N hN hl hc
  refine ⟨hN, ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog0 : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hgap : 2 * Real.log (N : ℝ) ^ B ≤ (N : ℝ) ^ (107 / 3498 : ℝ) := by
    calc
      2 * Real.log (N : ℝ) ^ B ≤
          (N : ℝ) ^ (107 / 6996 : ℝ) * (N : ℝ) ^ (107 / 6996 : ℝ) := by
        gcongr
      _ = (N : ℝ) ^ (107 / 3498 : ℝ) := by
        rw [← Real.rpow_add hN0]
        congr 1
        norm_num
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog0 B)).2
  calc
    2 * (N : ℝ) ^ (821 / 1749 : ℝ) * Real.log (N : ℝ) ^ B =
        (2 * Real.log (N : ℝ) ^ B) * (N : ℝ) ^ (821 / 1749 : ℝ) := by ring
    _ ≤ (N : ℝ) ^ (107 / 3498 : ℝ) * (N : ℝ) ^ (821 / 1749 : ℝ) :=
      mul_le_mul_of_nonneg_right hgap (Real.rpow_nonneg hN0.le _)
    _ = (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.rpow_add hN0]
      congr 1
      norm_num

/-- The single cutoff pays the logarithmic loss and both natural rounding
boundaries, uniformly for every positive outer product up to `N^(13/33)`. -/
theorem goldbachOrderedPair_level_eventually (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ ∀ p : ℕ, 0 < p →
      (p : ℝ) ≤ (N : ℝ) ^ (13 / 33 : ℝ) →
      1 < LiuWeight.panModulusCutoff N B / p + 1 ∧
      ∀ ℓ ∈ (goldbachS1ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))).primeFactors,
        ℓ < LiuWeight.panModulusCutoff N B / p + 1 := by
  filter_upwards [OrderedPairLevel_eventually_real_bound B] with N hN
  refine ⟨hN.1, ?_⟩
  intro p hp hpu
  let z : ℝ := (N : ℝ) ^ (4 / 53 : ℝ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hz1 : 1 ≤ z := Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega))
    (by norm_num)
  have hz0 : 0 ≤ z := le_trans (by norm_num) hz1
  have hceil : (Nat.ceil z : ℝ) ≤ 2 * z := by
    have := Nat.ceil_lt_add_one hz0
    linarith
  have hproduct : p * Nat.ceil z ≤ LiuWeight.panModulusCutoff N B := by
    rw [LiuWeight.panModulusCutoff_eq_upper]
    apply Nat.le_floor
    calc
      ((p * Nat.ceil z : ℕ) : ℝ) = (p : ℝ) * Nat.ceil z := by simp
      _ ≤ (N : ℝ) ^ (13 / 33 : ℝ) * (2 * z) := by gcongr
      _ = 2 * (N : ℝ) ^ (821 / 1749 : ℝ) := by
        dsimp [z]
        rw [← mul_assoc, mul_comm ((N : ℝ) ^ (13 / 33 : ℝ)) 2, mul_assoc,
          ← Real.rpow_add hN0]
        congr 2
        norm_num
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ B := hN.2
      _ = AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer.upperConductor N B := by
        rw [AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer.upperConductor,
          AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer.lowConductor,
          Real.sqrt_eq_rpow]
  have hdiv : Nat.ceil z ≤ LiuWeight.panModulusCutoff N B / p :=
    (Nat.le_div_iff_mul_le hp).2 (by simpa [mul_comm] using hproduct)
  have hceil1 : 1 ≤ Nat.ceil z := by
    exact_mod_cast hz1.trans (Nat.le_ceil z)
  refine ⟨by omega, ?_⟩
  intro ℓ hℓ
  have hprime := Nat.mem_primeFactors.mp hℓ
  have hℓz : (ℓ : ℝ) < z :=
    ((prime_dvd_goldbachS1ProdPrimes_iff hprime.1).mp hprime.2.1).1
  have hℓceil : ℓ < Nat.ceil z := Nat.lt_ceil.mpr hℓz
  omega

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig