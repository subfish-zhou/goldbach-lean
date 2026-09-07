import MathlibNt.SieveTheory.LiLiuGoldbachWeightLogScale
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

/-- Pay the ambient-prime-divisor excess after the proved uniform Euler factor.
The prime-size threshold is uniform in every later tau in [0,1]. -/
theorem goldbachG11_buchstabExcess_paid (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
      8*(1+τ)^3*SingularSeries.liuSingularSeries N*
        (8400*(N : ℝ)/(N : ℝ)^(4/53 : ℝ))/Real.log (N : ℝ) ≤
      δ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨K,_,hpaid⟩ := goldbach_power_error_le_log_scale_eventually
    (8400*64) (4/53) δ (by norm_num) (by norm_num) hδ
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  obtain ⟨L,hL⟩ := eventually_atTop.mp hl
  refine ⟨max 4 (max K L),le_max_left _ _,?_⟩
  intro N hN τ hτ hτ1
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hKL := (le_max_right _ _).trans hN
  have hlog1 := hL N ((le_max_right _ _).trans hKL)
  have hlog0 : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hc : 8*(1+τ)^3 ≤ 64 := by
    have hh : (1+τ)^3 ≤ (2 : ℝ)^3 := pow_le_pow_left₀ (by positivity) (by linarith) _
    nlinarith
  have hp : (8400*64)*(N : ℝ)/(N : ℝ)^(4/53 : ℝ) ≤ δ*(N : ℝ)/Real.log (N : ℝ)^2 := by
    have hh := hpaid N ((le_max_left _ _).trans hKL) (4/53) le_rfl
    rw [Real.rpow_sub hN0,Real.rpow_one] at hh
    simpa only [mul_div_assoc] using hh
  have hmass : 0 ≤ SingularSeries.liuSingularSeries N*(8400*(N : ℝ)/(N : ℝ)^(4/53 : ℝ)) := by
    exact mul_nonneg (SingularSeries.liuSingularSeries_pos N).le (by positivity)
  calc
    _ = 8*(1+τ)^3*(SingularSeries.liuSingularSeries N*
          (8400*(N : ℝ)/(N : ℝ)^(4/53 : ℝ)))/Real.log (N : ℝ) := by ring
    _ ≤ 64*(SingularSeries.liuSingularSeries N*
          (8400*(N : ℝ)/(N : ℝ)^(4/53 : ℝ)))/Real.log (N : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hmass) hlog0.le
    _ ≤ 64*(SingularSeries.liuSingularSeries N*
          (8400*(N : ℝ)/(N : ℝ)^(4/53 : ℝ))) := div_le_self (by positivity) hlog1
    _ = SingularSeries.liuSingularSeries N*((8400*64)*(N : ℝ)/(N : ℝ)^(4/53 : ℝ)) := by ring
    _ ≤ SingularSeries.liuSingularSeries N*(δ*(N : ℝ)/Real.log (N : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hp (SingularSeries.liuSingularSeries_pos N).le
    _ = _ := by ring

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig