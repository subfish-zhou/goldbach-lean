import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4TwoCharacterFixedWitness
import MathlibNt.AnalyticNumberTheory.Siegel.Bombieri1965Theorem4QuadraticSmallValueRealZero

/-!
# A conductor-uniform lower bound for actual quadratic L-values

This modern fixed-witness argument proves the Siegel lower bound without an
assumed zero-repulsion, exceptional-zero, or L-value lower-bound premise.
Either a fixed left neighborhood has no primitive quadratic real zero, or
one actual witness in that neighborhood is chosen before every target.
-/

open Complex

namespace AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4

open DirichletCharacter

/-- For each positive exponent, one positive constant bounds the actual
L-value of every primitive nonprincipal quadratic character, at every
nonzero conductor. The constant is not asserted to be effective. -/
theorem exists_uniform_quadratic_LFunction_one_lower_bound
    (η : ℝ) (hη : 0 < η) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 → χ ^ 2 = 1 →
        c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re := by
  obtain ⟨ε₀, hε₀, _hε₀4, hsmall⟩ :=
    exists_uniform_small_value_real_zero_neighborhood
  let ε : ℝ := min ε₀ (min (1 / 8) (η / 100))
  have hε : 0 < ε := lt_min hε₀ (lt_min (by norm_num) (by positivity))
  have hε₀bound : ε ≤ ε₀ := min_le_left _ _
  have hε8 : ε ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hεη : ε ≤ η / 100 := (min_le_right _ _).trans (min_le_right _ _)
  by_cases hw : ∃ (r : ℕ) (_ : NeZero r) (ψ : DirichletCharacter ℂ r) (β : ℝ),
      ψ.IsPrimitive ∧ ψ ≠ 1 ∧ ψ ^ 2 = 1 ∧
        β ∈ Set.Ioo (1 - ε) 1 ∧ ψ.LFunction (β : ℂ) = 0
  · obtain ⟨r, hr, ψ, β, hψprim, hψ, hψquad, hβ, hzero⟩ := hw
    obtain ⟨c, hc, hcomp⟩ := exists_fixed_witness_lower_bound
      ψ hψprim hψ hψquad (by linarith [hβ.1] : 7 / 8 ≤ β)
      hβ.2 hzero (by positivity : 0 < η / 6)
    refine ⟨c, hc, ?_⟩
    intro q _ χ hχprim hχ hχquad
    have hq : (1 : ℝ) ≤ q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hp : (q : ℝ) ^ (-η) ≤
        (q : ℝ) ^ (-(24 * (1 - β) + 3 * (η / 6))) :=
      Real.rpow_le_rpow_of_exponent_le hq (by linarith [hβ.1])
    exact (mul_le_mul_of_nonneg_left hp hc.le).trans (hcomp q χ hχprim hχ hχquad)
  · let c : ℝ := ε / (4 * (648 : ℝ) ^ (4 * ε))
    have hc : 0 < c := by dsimp [c]; positivity
    refine ⟨c, hc, ?_⟩
    intro q hqinst χ hχprim hχ hχquad
    have hq : (1 : ℝ) ≤ q := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
    have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
    have hlarge : ε / (4 * (648 * (q : ℝ)) ^ (4 * ε)) <
        (χ.LFunction 1).re := by
      by_contra h
      obtain ⟨β, hβ, hzero⟩ := hsmall ε hε hε₀bound q χ hχprim hχ hχquad (not_lt.mp h)
      exact hw ⟨q, hqinst, χ, β, hχprim, hχ, hχquad, hβ, hzero⟩
    have hthreshold :
        c * (q : ℝ) ^ (-(4 * ε)) = ε / (4 * (648 * (q : ℝ)) ^ (4 * ε)) := by
      dsimp [c]
      simp only [Real.rpow_neg hq0.le,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 648) hq0.le,
        div_eq_mul_inv, mul_inv_rev]
      ring
    calc
      c * (q : ℝ) ^ (-η) ≤ c * (q : ℝ) ^ (-(4 * ε)) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hq (by linarith)) hc.le
      _ = _ := hthreshold
      _ ≤ _ := hlarge.le

end AnalyticNumberTheory.LargeSieve.Bombieri1965Theorem4
