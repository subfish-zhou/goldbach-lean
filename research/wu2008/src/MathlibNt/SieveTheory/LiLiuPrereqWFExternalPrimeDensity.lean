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


#check progressionDensity_isMultiplicative
#print axioms progressionDensity_isMultiplicative
#check primeDensity_densityNumerator
#print axioms primeDensity_densityNumerator

end MathlibNt.SieveTheory.LiLiuPrereqWF
