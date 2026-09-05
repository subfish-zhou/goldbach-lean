import MathlibNt.AnalyticNumberTheory.LargeSieve.FourFactorUnconditionalEndpoints

/-! Actual prime counting, extracted only from the q=1 term of Standard BV.
The fixed normalization is κ₀=2/log 2. Real endpoint changes are paid by an
integrable short interval, not by replacing the logarithmic integral argument. -/
namespace AnalyticNumberTheory.LargeSieve.PanPrincipal
open Classical Finset Filter
open MathlibNt.SieveTheory.BombieriVinogradov MathlibNt.SieveTheory.LiuWeight
open scoped BigOperators Topology
noncomputable section

def primeCount (t : ℕ) : ℝ :=
  ∑ p ∈ range (t + 1), if p.Prime then (1 : ℝ) else 0

theorem primeCount_sub_li_eq_standard (t : ℕ) :
    primeCount t - liuLogarithmicIntegral (2 / Real.log 2) t =
      standardPrimeAPError t 1 0 := by
  simp [primeCount, standardPrimeAPError, primesInAP, trueLogarithmicIntegral,
    Nat.ModEq, Finset.sum_boole]
  congr 1
  apply Finset.filter_congr
  intro p _hp
  simp only [Nat.mod_one, and_true]

/-- A positive real power dominates any prescribed logarithmic power. -/
theorem eventually_log_rpow_le_rpow (b d : ℝ) (hd : 0 < d) :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ b ≤ (N : ℝ) ^ d := by
  have h := (isLittleO_log_rpow_rpow_atTop b hd).bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h,
    eventually_ge_atTop (2 : ℕ)] with N hN hN2
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog _),
    abs_of_nonneg (Real.rpow_nonneg hpos.le _), one_mul] using hN

theorem eventually_one_le_panModulusCutoff (b : ℝ) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ panModulusCutoff N b := by
  filter_upwards [eventually_log_rpow_le_rpow b (1 / 2) (by norm_num),
    eventually_ge_atTop (2 : ℕ)] with N h hN
  apply Nat.le_floor
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  simpa only [Nat.cast_one] using (one_le_div (Real.rpow_pos_of_pos hlog b)).mpr h

/-- No PNT hypothesis: the literal Standard BV q=1/residue=0 finite specialization. -/
theorem primeCount_li_pnt (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∃ M : ℕ, ∀ t ≥ M,
      |primeCount t - liuLogarithmicIntegral (2 / Real.log 2) t| ≤
        C * (t : ℝ) / Real.log (t : ℝ) ^ s := by
  obtain ⟨b, _hb, C, hC, hBV⟩ := fourFactor_standardBombieriVinogradov s hs
  refine ⟨C, hC, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [hBV, eventually_one_le_panModulusCutoff b,
    eventually_ge_atTop (2 : ℕ)] with t ht hcut ht2
  rw [primeCount_sub_li_eq_standard, ← standardPrimeAPMaxError_one]
  calc
    _ ≤ standardPrimeAPPrefixMaxError t 1 := standardPrimeAPMaxError_le_prefixMaxError t 1
    _ ≤ ∑ q ∈ Icc 1 (panModulusCutoff t b), standardPrimeAPPrefixMaxError t q :=
      single_le_sum (fun q _ => standardPrimeAPPrefixMaxError_nonneg t q)
        (mem_Icc.mpr ⟨le_rfl, hcut⟩)
    _ ≤ _ := ht ht2

/-- Actual short-interval bound for Liu's Li, uniformly in its additive normalization. -/
theorem abs_li_sub_le_short (κ : ℝ) {x y : ℝ}
    (hx : 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ x + 1) :
    |liuLogarithmicIntegral κ y - liuLogarithmicIntegral κ x| ≤ 1 / Real.log 2 := by
  have hi := liuLogarithmicIntegrand_intervalIntegrable_of_two_le hx hxy
  have he := intervalIntegral.integral_add_adjacent_intervals
    (liuLogarithmicIntegrand_intervalIntegrable hx) hi
  have hn : 0 ≤ ∫ t in x..y, 1 / Real.log t := by
    apply intervalIntegral.integral_nonneg hxy
    intro t ht
    exact liuLogarithmicIntegrand_nonneg (hx.trans ht.1)
  have hb : (∫ t in x..y, 1 / Real.log t) ≤ (y - x) * (1 / Real.log 2) := by
    calc
      _ ≤ ∫ _t in x..y, 1 / Real.log 2 := by
        apply intervalIntegral.integral_mono_on hxy hi intervalIntegrable_const
        intro t ht
        apply one_div_le_one_div_of_le (Real.log_pos (by norm_num : (1 : ℝ) < 2))
        exact Real.log_le_log (by norm_num) (hx.trans ht.1)
      _ = _ := by simp [intervalIntegral.integral_const, smul_eq_mul]
  have hid : liuLogarithmicIntegral κ y - liuLogarithmicIntegral κ x =
      ∫ t in x..y, 1 / Real.log t := by
    unfold liuLogarithmicIntegral
    linarith
  rw [hid, abs_of_nonneg hn]
  refine hb.trans ?_
  exact (mul_le_mul_of_nonneg_right (by linarith : y - x ≤ 1)
    (by positivity)).trans_eq (one_mul _)

/-- Natural floor to real quotient: the missing interval has length strictly less than one. -/
theorem abs_li_real_div_sub_nat_div (κ : ℝ) {N a : ℕ}
    (ha : 0 < a) (ht : 2 ≤ N / a) :
    |liuLogarithmicIntegral κ ((N : ℝ) / a) - liuLogarithmicIntegral κ (N / a : ℕ)| ≤
      1 / Real.log 2 := by
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  apply abs_li_sub_le_short κ (by exact_mod_cast ht)
  · apply (le_div_iff₀ haR).mpr
    exact_mod_cast Nat.div_mul_le_self N a
  · apply (div_le_iff₀ haR).mpr
    have h : (N : ℝ) < (N / a : ℕ) * (a : ℝ) + a := by
      exact_mod_cast Nat.lt_div_mul_add ha (a := N)
    nlinarith

/-- PNT with the real quotient Li argument, still scaled at the natural quotient. -/
theorem primeCount_li_real_div_pnt (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∃ M : ℕ, ∀ N a : ℕ, 0 < a → M ≤ N / a →
      |primeCount (N / a) - liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / a)| ≤
        C * (N / a : ℕ) / Real.log (N / a : ℕ) ^ s := by
  obtain ⟨C, hC, M, hpnt⟩ := primeCount_li_pnt s hs
  obtain ⟨M', hM'⟩ := eventually_atTop.mp (eventually_log_rpow_le_rpow s 1 (by norm_num))
  refine ⟨C + 1 / Real.log 2, by positivity, max 2 (max M M'), ?_⟩
  intro N a ha ht
  have ht2 : 2 ≤ N / a := (le_max_left _ _).trans ht
  have htM : M ≤ N / a := (le_trans (le_max_left _ _) (le_max_right _ _)).trans ht
  have htM' : M' ≤ N / a := (le_trans (le_max_right _ _) (le_max_right _ _)).trans ht
  have hlog : 0 < Real.log (N / a : ℕ) := Real.log_pos (by exact_mod_cast (show 1 < N / a by omega))
  have hpow := hM' (N / a) htM'
  rw [Real.rpow_one] at hpow
  have hcorr : 1 / Real.log 2 ≤ (1 / Real.log 2) * (N / a : ℕ) /
      Real.log (N / a : ℕ) ^ s := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog s)).mpr
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  calc
    _ ≤ |primeCount (N / a) - liuLogarithmicIntegral (2 / Real.log 2) (N / a : ℕ)| +
        |liuLogarithmicIntegral (2 / Real.log 2) (N / a : ℕ) -
          liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / a)| := abs_sub_le _ _ _
    _ ≤ C * (N / a : ℕ) / Real.log (N / a : ℕ) ^ s + 1 / Real.log 2 := by
      apply add_le_add (hpnt (N / a) htM)
      rw [abs_sub_comm]
      exact abs_li_real_div_sub_nat_div _ ha ht2
    _ ≤ _ := by
      calc
        _ ≤ C * (N / a : ℕ) / Real.log (N / a : ℕ) ^ s +
            (1 / Real.log 2) * (N / a : ℕ) / Real.log (N / a : ℕ) ^ s := add_le_add_right hcorr _
        _ = _ := by ring

end
end AnalyticNumberTheory.LargeSieve.PanPrincipal