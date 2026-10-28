import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryResonanceCount

/-!
# Uniform local-scale payment for the resonance divisor count

The proven pointwise divisor estimate pays both finite divisor choices.
The bounds are uniform in the common first beta index and signed product.
`A` bounds `|P|`, and `B` bounds `d₁*n + |P|`; no dyadic parameters
are confused with the original, unextracted beta coordinates.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem iv3_resonance_divisor_sum_le_local_scales
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d₁ n : ℕ) (P : ℤ) (A B : ℝ),
      0 ≤ A → 0 ≤ B → (P.natAbs : ℝ) ≤ A →
      ((d₁ * n + P.natAbs : ℕ) : ℝ) ≤ B →
      (∑ j ∈ P.natAbs.divisors,
        (fouvryTau 2 (P * ((d₁ : ℤ) * n - j)).natAbs : ℝ)) ≤
        C * A ^ (2 * ε) * B ^ ε := by
  obtain ⟨C, hC, hτ⟩ := fouvryTau_le_const_rpow (k := 2) (by omega) hε
  have hτall (m : ℕ) : (fouvryTau 2 m : ℝ) ≤ C * (m : ℝ) ^ ε := by
    obtain rfl | hm := eq_or_ne m 0
    · simp only [fouvryTau_zero, Nat.cast_zero]
      exact mul_nonneg hC.le (Real.rpow_nonneg (by rfl) _)
    · exact hτ m (Nat.pos_of_ne_zero hm)
  refine ⟨C ^ 2, by positivity, ?_⟩
  intro d₁ n P A B hA hB hPA hDB
  have hsmall (j : ℕ) (hj : j ∈ P.natAbs.divisors) :
      (fouvryTau 2 (P * ((d₁ : ℤ) * n - j)).natAbs : ℝ) ≤
        C * (A * B) ^ ε := by
    have hjle : j ≤ P.natAbs :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hj).2)
        (Nat.mem_divisors.mp hj).1
    have hd : ((d₁ : ℤ) * n - j).natAbs ≤ d₁ * n + P.natAbs := by
      calc
        _ ≤ d₁ * n + j := by
          simpa only [Int.natAbs_mul, Int.natAbs_natCast] using
            Int.natAbs_sub_le ((d₁ : ℤ) * n) j
        _ ≤ _ := Nat.add_le_add_left hjle _
    have hprod : ((P * ((d₁ : ℤ) * n - j)).natAbs : ℝ) ≤ A * B := by
      rw [Int.natAbs_mul, Nat.cast_mul]
      exact mul_le_mul hPA
        ((show (((d₁ : ℤ) * n - j).natAbs : ℝ) ≤
          ((d₁ * n + P.natAbs : ℕ) : ℝ) by exact_mod_cast hd).trans hDB)
        (by positivity) hA
    exact (hτall _).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hprod hε.le) hC.le)
  have hcount : (fouvryTau 2 P.natAbs : ℝ) ≤ C * A ^ ε :=
    (hτall _).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by positivity) hPA hε.le) hC.le)
  calc
    _ ≤ ∑ _j ∈ P.natAbs.divisors, C * (A * B) ^ ε := sum_le_sum hsmall
    _ = (fouvryTau 2 P.natAbs : ℝ) * (C * (A * B) ^ ε) := by
      simp [fouvryTau_two]
    _ ≤ (C * A ^ ε) * (C * (A * B) ^ ε) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = C ^ 2 * A ^ (2 * ε) * B ^ ε := by
      rw [Real.mul_rpow hA hB]
      have he : A ^ (2 * ε) = (A ^ ε) ^ 2 := by
        rw [mul_comm (2 : ℝ) ε, Real.rpow_mul hA, Real.rpow_two]
      rw [he]
      ring


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
