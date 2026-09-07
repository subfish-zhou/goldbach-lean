import MathlibNt.SieveTheory.LiLiuPrereqWFExternalTransport

/-!
# The literal prime-progression density in the omega(d)/d convention

The inverse totient is retained on prime powers. No squarefree extension is
substituted in either the full-modulus remainder or the density numerator.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open ArithmeticFunction SmallRosser

noncomputable def densityNumerator (g : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => (n : ℝ) * g n, by simp⟩

theorem densityNumerator_isMultiplicative {g : ArithmeticFunction ℝ}
    (hg : g.IsMultiplicative) : (densityNumerator g).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [densityNumerator, hg.map_one]
  · intro m n hmn
    change ((m * n : ℕ) : ℝ) * g (m * n) = ((m : ℝ) * g m) * ((n : ℝ) * g n)
    rw [hg.map_mul_of_coprime hmn, Nat.cast_mul]
    ring

@[simp]
theorem primeDensity_densityNumerator (g : ArithmeticFunction ℝ) :
    primeDensity (densityNumerator g) = g := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    change (n : ℝ) * g n / n = g n
    field_simp

theorem progressionDensity_isMultiplicative (a : ℕ) :
    (progressionDensity a).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simp [progressionDensity]
  · intro m n hmn
    simp only [progressionDensity, ArithmeticFunction.coe_mk,
      Nat.coprime_mul_iff_left, Nat.totient_mul hmn, Nat.cast_mul]
    split_ifs <;> simp_all [mul_comm]

theorem progressionDensity_prime_bounds (a : ℕ) {p : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) :
    0 ≤ progressionDensity a p ∧ progressionDensity a p < 1 := by
  change 0 ≤ (if p.Coprime a then (p.totient : ℝ)⁻¹ else 0) ∧
    (if p.Coprime a then (p.totient : ℝ)⁻¹ else 0) < 1
  by_cases hpa : p.Coprime a
  · simp only [if_pos hpa, Nat.totient_prime hp]
    have hp' : (2 : ℝ) < p := by exact_mod_cast hp2
    have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 :=
      by simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) hp.one_le)
    rw [hcast]
    constructor
    · exact inv_nonneg.mpr (by linarith)
    · exact (inv_lt_one₀ (by linarith)).mpr (by linarith)
  · simp [hpa]

#check progressionDensity_isMultiplicative
#print axioms progressionDensity_isMultiplicative
#check primeDensity_densityNumerator
#print axioms primeDensity_densityNumerator

end MathlibNt.SieveTheory.LiLiuPrereqWF
