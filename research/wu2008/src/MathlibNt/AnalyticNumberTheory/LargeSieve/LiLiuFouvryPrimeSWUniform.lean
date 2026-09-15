import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeSWLogSaving

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open Finset Filter
open scoped Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory MathlibNt.SieveTheory.Richert1969
noncomputable section

/-- A uniform natural-scale estimate for all moduli and all moving prime intervals.
The constants and the scale threshold precede both endpoints and every arithmetic parameter. -/
theorem primeSW_uniform_eventually (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ u v : ℝ, u ≤ v → ⌊u⌋₊ ∈ Icc 2 N → ⌊v⌋₊ ∈ Icc 2 N →
      ∀ d h : ℕ, 0 < d → 0 < h → ∀ b : ℕ, b.Coprime d →
      |betaCoprimeAPDiscrepancy (primeSWInterval u v) primeSWBeta d h b| ≤
        C * (N : ℝ) * (fouvryTau 2 h : ℝ) / Real.log N ^ B := by
  obtain ⟨c, hc, k, hk, hBV⟩ := richert418 (B + 1 : ℝ) (by positivity)
  have hcR := richertReciprocalTotientConstant_pos
  let C := 4 * k + 5 + 2 * richertReciprocalTotientConstant
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hpay : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ (B + 1 + B) ≤ N := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      primeSW_log_rpow_eventually ((B + 1 + B : ℕ) : ℝ) (s := 1) (by norm_num)
  have hpow : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ (B + 1) ≤ N := by
    simpa only [Real.rpow_natCast, Real.rpow_one] using
      primeSW_log_rpow_eventually ((B + 1 : ℕ) : ℝ) (s := 1) (by norm_num)
  filter_upwards [hBV, hpay, hpow, primeSW_log_cutoff_eventually (B + 1) c,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1,
    eventually_ge_atTop (3 : ℕ)] with N hBV hpay hpow hcut hl hN
  intro u v huv hu hv d h hd hh b hb
  let L := Real.log (N : ℝ)
  let Q := (N : ℝ) / L ^ B
  let t := (fouvryTau 2 h : ℝ)
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hl
  have ht : 1 ≤ t := by
    dsimp [t]
    rw [fouvryTau_two]
    exact_mod_cast Finset.one_le_card.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd h, by omega⟩⟩
  have ht0 : 0 ≤ t := by linarith
  have hLB : L ^ B ≤ L ^ (B + 1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg hL.le _) hl
  have hQ : 1 ≤ Q := (le_div_iff₀ (pow_pos hL _)).mpr (by dsimp [L] at *; linarith)
  have hQ0 : 0 ≤ Q := by linarith
  have hQt : Q ≤ Q * t := le_mul_of_one_le_right hQ0 ht
  have htQ : t ≤ Q * t := le_mul_of_one_le_left ht0 hQ
  change |betaCoprimeAPDiscrepancy (primeSWInterval u v) primeSWBeta d h b| ≤
    C * (N : ℝ) * t / L ^ B
  rw [show C * (N : ℝ) * t / L ^ B = C * (Q * t) by dsimp [Q]; ring]
  by_cases hsmall : (d : ℝ) ≤ L ^ (B + 1)
  · have hcutd := hcut d hsmall
    have hcut1 : 1 ≤ LiuWeight.panModulusCutoff N c := le_trans hd hcutd
    have herr (q : ℕ) (hq : q ∈ Icc 1 (LiuWeight.panModulusCutoff N c)) :
        primeAPPrefixMaxError N q ≤ k * Q := by
      have hp := (single_le_sum (fun q _ => primeAPPrefixMaxError_nonneg N q) hq).trans
        (hBV (by omega))
      have he : Real.log (N : ℝ) ^ (B + 1 : ℝ) = L ^ (B + 1) := by
        rw [show (B + 1 : ℝ) = ((B + 1 : ℕ) : ℝ) by simp, Real.rpow_natCast]
      rw [he] at hp
      exact hp.trans ((div_le_div_of_nonneg_left (by positivity : 0 ≤ k * (N : ℝ))
        (pow_pos hL _) hLB).trans_eq (by dsimp [Q]; ring))
    have hdQ : (d : ℝ) ≤ Q := by
      apply (le_div_iff₀ (pow_pos hL _)).mpr
      calc
        (d : ℝ) * L ^ B ≤ L ^ (B + 1) * L ^ B :=
          mul_le_mul_of_nonneg_right hsmall (pow_nonneg hL.le _)
        _ = L ^ (B + 1 + B) := (pow_add _ _ _).symm
        _ ≤ _ := hpay
    have hraw := primeSW_interval_discrepancy_bound huv hu hv hd hh hb
    have heD := herr d (mem_Icc.mpr ⟨hd, hcutd⟩)
    have he1 := herr 1 (mem_Icc.mpr ⟨le_rfl, hcut1⟩)
    have hkQ : k * Q ≤ k * (Q * t) := mul_le_mul_of_nonneg_left hQt hk.le
    have hc0 := richertReciprocalTotientConstant_pos
    have hQt0 : 0 ≤ Q * t := mul_nonneg hQ0 ht0
    dsimp [C]
    nlinarith
  · have hS : primeSWInterval u v ⊆ range (N + 1) := by
      intro n hn
      have hn' := (mem_Ioc.mp hn).2
      exact mem_range.mpr (by have := (mem_Icc.mp hv).2; omega)
    have hraw := primeSW_large_log_bound B hN hl hpow hd (le_of_lt (lt_of_not_ge hsmall))
      (primeSWInterval u v) hS h b
    have hc0 := richertReciprocalTotientConstant_pos
    have hcoef : 0 ≤ 2 + 2 * richertReciprocalTotientConstant := by positivity
    have hmul := mul_le_mul_of_nonneg_left hQt hcoef
    have hQt0 : 0 ≤ Q * t := mul_nonneg hQ0 ht0
    have he : (2 + 2 * richertReciprocalTotientConstant) * (N : ℝ) / Real.log N ^ B =
        (2 + 2 * richertReciprocalTotientConstant) * Q := by dsimp [Q, L]; ring
    rw [he] at hraw
    dsimp [C]
    nlinarith

end
end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
