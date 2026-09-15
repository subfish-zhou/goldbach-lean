import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryPrimeSWLarge

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open Finset Filter
open scoped Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory MathlibNt.SieveTheory.Richert1969
noncomputable section

/-- Fixed logarithmic powers are eventually dominated uniformly in the scale. -/
theorem primeSW_log_rpow_eventually (a : ℝ) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ a ≤ (N : ℝ) ^ s := by
  have hb := (isLittleO_log_rpow_rpow_atTop a hs).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hb,
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually_ge_atTop 1]
    with N hN hN1
  simpa only [Real.norm_eq_abs, one_mul,
    abs_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hN1) _),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] using hN

/-- Every fixed logarithmic modulus range lies inside the genuine BV cutoff. -/
theorem primeSW_log_cutoff_eventually (K : ℕ) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ, (d : ℝ) ≤ Real.log N ^ K →
      d ≤ LiuWeight.panModulusCutoff N C := by
  filter_upwards [primeSW_log_rpow_eventually ((K : ℝ) + C)
    (by norm_num : (0 : ℝ) < 1 / 2), eventually_ge_atTop (2 : ℕ)] with N hpow hN
  intro d hd
  have hl : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  apply Nat.le_floor
  apply (le_div_iff₀ (Real.rpow_pos_of_pos hl C)).mpr
  calc
    (d : ℝ) * Real.log N ^ C ≤ Real.log N ^ K * Real.log N ^ C :=
      mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg hl.le C)
    _ = Real.log N ^ ((K : ℝ) + C) := by rw [Real.rpow_add hl, Real.rpow_natCast]
    _ ≤ _ := hpow

/-- The large-modulus envelope is uniformly logarithmically small, including d>N. -/
theorem primeSW_large_log_bound (B : ℕ) {N d : ℕ}
    (hN : 3 ≤ N) (hl : 1 ≤ Real.log (N : ℝ))
    (hpow : Real.log (N : ℝ) ^ (B + 1) ≤ N)
    (hd : 0 < d) (hlarge : Real.log (N : ℝ) ^ (B + 1) ≤ d)
    (S : Finset ℕ) (hS : S ⊆ range (N + 1)) (h b : ℕ) :
    |betaCoprimeAPDiscrepancy S primeSWBeta d h b| ≤
      (2 + 2 * richertReciprocalTotientConstant) * (N : ℝ) / Real.log N ^ B := by
  let L := Real.log (N : ℝ)
  let c := richertReciprocalTotientConstant
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one hl
  have hc : 0 ≤ c := richertReciprocalTotientConstant_pos.le
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hmin : L ^ (B + 1) ≤ (min d N : ℕ) := by
    rw [Nat.cast_min]
    exact le_min hlarge hpow
  have hmin0 : (0 : ℝ) < (min d N : ℕ) := lt_of_lt_of_le (pow_pos hL _) hmin
  have hLB : L ^ B ≤ L ^ (B + 1) := by
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg hL.le _) hl
  have hbudget : 1 ≤ (N : ℝ) / L ^ B := (le_div_iff₀ (pow_pos hL _)).mpr (by linarith)
  have hAP : (N : ℝ) / d ≤ (N : ℝ) / L ^ B :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg N) (pow_pos hL _) (hLB.trans hlarge)
  have hphi : c * L / (min d N : ℕ) ≤ c / L ^ B := by
    apply (div_le_div_iff₀ hmin0 (pow_pos hL _)).mpr
    calc
      c * L * L ^ B = c * L ^ (B + 1) := by rw [pow_succ]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hmin hc
  have hm : ((N : ℝ) + 1) * (c * L / (min d N : ℕ)) ≤
      2 * c * ((N : ℝ) / L ^ B) := by
    calc
      _ ≤ ((N : ℝ) + 1) * (c / L ^ B) := mul_le_mul_of_nonneg_left hphi (by positivity)
      _ ≤ (2 * (N : ℝ)) * (c / L ^ B) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  have henv := primeSW_large_modulus_envelope hN hd S hS h b
  change |betaCoprimeAPDiscrepancy S primeSWBeta d h b| ≤
    (2 + 2 * c) * (N : ℝ) / L ^ B
  change |betaCoprimeAPDiscrepancy S primeSWBeta d h b| ≤
    (N : ℝ) / d + 1 + ((N : ℝ) + 1) * (c * L / (min d N : ℕ)) at henv
  calc
    _ ≤ (N : ℝ) / L ^ B + (N : ℝ) / L ^ B + 2 * c * ((N : ℝ) / L ^ B) :=
      henv.trans (add_le_add (add_le_add hAP hbudget) hm)
    _ = _ := by ring

end
end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
