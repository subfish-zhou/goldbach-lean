import MathlibNt.SieveTheory.LiLiuGoldbachG11SieveParameters

open Filter
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- Pay the actual weighted small-output term, uniformly in the later sieve cutoff. -/
theorem goldbachG11_smallOutput_paid (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ Z : ℝ, 0 ≤ Z →
      Z ≤ (N : ℝ)^((1 : ℝ)/4) →
      8000*(Nat.ceil Z : ℝ) ≤
        δ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨K,_,hpaid⟩ := goldbach_power_error_le_log_scale_eventually
    16000 (3/4) (δ*SingularSeries.liuUniversalProduct) (by norm_num) (by norm_num)
    (mul_pos hδ SingularSeries.liuUniversalProduct_pos)
  refine ⟨max 4 K,le_max_left _ _,?_⟩
  intro N hN Z hZ hZu
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hquarter : (1 : ℝ) ≤ (N : ℝ)^((1 : ℝ)/4) := Real.one_le_rpow hN1 (by norm_num)
  have hceil : (Nat.ceil Z : ℝ) ≤ 2*(N : ℝ)^((1 : ℝ)/4) := by
    have hh := (Nat.ceil_lt_add_one hZ).le
    linarith
  have hp : 16000*(N : ℝ)^((1 : ℝ)/4) ≤
      (δ*SingularSeries.liuUniversalProduct)*(N : ℝ)/Real.log (N : ℝ)^2 := by
    convert hpaid N ((le_max_right _ _).trans hN) (3/4) le_rfl using 1
    norm_num
  have hs := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hδ.le)
    (show 0 ≤ (N : ℝ)/Real.log (N : ℝ)^2 by positivity)
  calc
    _ ≤ 16000*(N : ℝ)^((1 : ℝ)/4) := by linarith
    _ ≤ _ := hp
    _ ≤ _ := by convert hs using 1 <;> first | rfl | ring


end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig