

import MathlibNt.AnalyticNumberTheory.LargeSieve.ConductorChangeLevelLedger

/-!
 # Linear-polylogarithmic control of imprimitive conductor multiplicity

This independent strengthening replaces the quadratic fibre estimate by the
average order of the divisor function.  The proof is completely finite:
`n = ∑ d ∣ n, φ(d)` bounds `n / φ(n)` by the number of divisors, the divisor
sum is transposed, and the resulting harmonic sum is bounded by a telescoping
logarithm.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- A finite harmonic factor, including exactly the terms `1, ..., R`. -/
def conductorHarmonicFactor (R : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 R, (e : ℝ)⁻¹

theorem conductorHarmonicFactor_nonneg (R : ℕ) :
    0 ≤ conductorHarmonicFactor R := by
  unfold conductorHarmonicFactor
  positivity


private theorem harmonic_step (k : ℕ) (hk : 0 < k) :
    (((k + 1 : ℕ) : ℝ)⁻¹) ≤
      Real.log ((k + 1 : ℕ) : ℝ) - Real.log (k : ℝ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkspos : (0 : ℝ) < k + 1 := by positivity
  have hratio : (0 : ℝ) < (k : ℝ) / (k + 1 : ℝ) := div_pos hkpos hkspos
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (ne_of_gt hkpos) (ne_of_gt hkspos)] at hlog
  have hid : (k : ℝ) / (k + 1 : ℝ) - 1 = -((k + 1 : ℝ)⁻¹) := by
    field_simp
    ring
  rw [hid] at hlog
  norm_num only [Nat.cast_add, Nat.cast_one] at hlog ⊢
  linarith

/-- The elementary telescoping logarithm bound for the finite harmonic factor. -/
theorem conductorHarmonicFactor_le (R : ℕ) :
    conductorHarmonicFactor R ≤ 1 + Real.log (R : ℝ) := by
  induction R with
  | zero => simp [conductorHarmonicFactor]
  | succ R ih =>
      by_cases hR : R = 0
      · subst R; norm_num [conductorHarmonicFactor]
      · rw [conductorHarmonicFactor, Finset.sum_Icc_succ_top (by omega)]
        rw [conductorHarmonicFactor] at ih
        have hs := harmonic_step R (Nat.pos_of_ne_zero hR)
        norm_num only [Nat.cast_add, Nat.cast_one] at hs ⊢
        linarith

/-- Divisor-sum control of one totient ratio. -/
theorem totientRatio_le_card_divisors (n : ℕ) (hn : 0 < n) :
    (n : ℝ) / (n.totient : ℝ) ≤ (n.divisors.card : ℝ) := by
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr hn
  nth_rw 1 [← Nat.sum_totient n]
  rw [Nat.cast_sum, Finset.sum_div]
  calc
    (∑ d ∈ n.divisors, (d.totient : ℝ) / (n.totient : ℝ))
      ≤ ∑ _d ∈ n.divisors, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        apply (div_le_one hφ).2
        exact_mod_cast Nat.le_of_dvd (Nat.totient_pos.mpr hn)
          (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = (n.divisors.card : ℝ) := by simp

/-- For fixed positive `e`, count its multiples up to `R`. -/
theorem sum_dvd_indicator_Icc (R e : ℕ) (he : 0 < e) :
    (∑ r ∈ Finset.Icc 1 R, if e ∣ r then (1 : ℝ) else 0) = (R / e : ℕ) := by
  symm
  rw [← Finset.sum_filter]
  calc
    ((R / e : ℕ) : ℝ) = ∑ k ∈ Finset.Icc 1 (R / e), (1 : ℝ) := by simp
    _ = ∑ r ∈ (Finset.Icc 1 R).filter (fun r => e ∣ r), (1 : ℝ) := by
      refine Finset.sum_bij (fun k _ => e * k) ?_ ?_ ?_ ?_
      · intro k hk
        rw [Finset.mem_filter, Finset.mem_Icc]
        rw [Finset.mem_Icc] at hk
        exact ⟨⟨Nat.mul_pos he hk.1,
          (Nat.mul_le_mul_left e hk.2).trans (Nat.mul_div_le R e)⟩,
          dvd_mul_right e k⟩
      · intro k₁ hk₁ k₂ hk₂ h
        exact Nat.eq_of_mul_eq_mul_left he h
      · intro r hr
        rw [Finset.mem_filter, Finset.mem_Icc] at hr
        refine ⟨r / e, ?_, ?_⟩
        · rw [Finset.mem_Icc]
          exact ⟨Nat.div_pos (Nat.le_of_dvd hr.1.1 hr.2) he,
            Nat.div_le_div_right hr.1.2⟩
        · exact Nat.mul_div_cancel' hr.2
      · intro k hk
        simp


end

end AnalyticNumberTheory.LargeSieve
