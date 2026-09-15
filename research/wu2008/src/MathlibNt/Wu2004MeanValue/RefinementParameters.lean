import MathlibNt.Wu2004MeanValue.OriginalCounts

/-!
# Fixing the small-product parameter before the asymptotic threshold

The accepted small-product constant is chosen before `eta`. The parameter
below is then fixed once, not allowed to vary with the later integer.
The separate unit payment uses the uniform singular-series lower bound.
-/

namespace Wu2004MeanValue

open Filter
open MathlibNt.SieveTheory.SingularSeries
noncomputable section

theorem exists_fixed_eta_small_product_upper (a ε : ℝ)
    (ha : 3 / 2 < a) (ha2 : a < 2) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ N₀ : ℕ,
      ∀ N : ℕ, N₀ ≤ N → Even N →
        (originalTripleCount N a η : ℝ) ≤
          ε * liuSingularSeries N * N / Real.log N ^ 2 := by
  obtain ⟨K, hK, hsmall⟩ := originalTripleCount_small_product_upper a ha ha2
  let η := min (1 / 4 : ℝ) (ε / (4 * K))
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηh : η < 1 / 2 := (min_le_left _ _).trans_lt (by norm_num)
  have hKη : K * η ≤ ε / 4 := by
    have hh := (le_div_iff₀ (show 0 < 4 * K by positivity)).mp
      (min_le_right (1 / 4 : ℝ) (ε / (4 * K)))
    dsimp only [η]
    nlinarith
  obtain ⟨N₀, hN₀⟩ := hsmall η hη hηh (ε / 2) (by positivity)
  refine ⟨η, hη, hηh, N₀, ?_⟩
  intro N hN hEven
  calc
    _ ≤ (K * η + ε / 2) * liuSingularSeries N * N / Real.log N ^ 2 :=
      hN₀ N hN hEven
    _ ≤ ε * liuSingularSeries N * N / Real.log N ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg N)
      exact mul_le_mul_of_nonneg_right (by linarith) (liuSingularSeries_pos N).le

theorem eventually_refinement_unit_paid (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (1 : ℝ) ≤ ε * liuSingularSeries N * N / Real.log N ^ 2 := by
  simpa only [Real.rpow_zero, mul_one] using
    eventually_powerSaving_le_singular_margin 1 0 ε (by norm_num) (by norm_num) hε

end
end Wu2004MeanValue
