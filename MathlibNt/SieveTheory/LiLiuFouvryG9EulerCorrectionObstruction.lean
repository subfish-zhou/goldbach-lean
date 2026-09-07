import MathlibNt.SieveTheory.LiLiuFouvryG9EulerCorrectionActual

noncomputable section
open Finset
open scoped Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The third box with rho=5/4 and index 4 contains only the integer 3. -/
theorem g9_third_box_four_eq_three {N i j : ℕ} {z : ℕ × ℕ}
    (hz : z ∈ fouvryG9LongLabels N (5 / 4) (i, j, 4)) : z.2 = 3 := by
  obtain ⟨_, _, _, _, _, _, _, hl, hu⟩ := mem_filter.mp hz
  change (5 / 4 : ℝ) ^ 4 ≤ (z.2 : ℝ) at hl
  change (z.2 : ℝ) < (5 / 4 : ℝ) ^ (4 + 1) at hu
  norm_num at hl hu
  have h2 : (2 : ℝ) < z.2 := by linarith
  have h4 : (z.2 : ℝ) < 4 := by linarith
  have h2n : 2 < z.2 := by exact_mod_cast h2
  have h4n : z.2 < 4 := by exact_mod_cast h4
  omega

/-- In this third box, the actual Euler product for P={3} is exactly one
on every nonzero long coefficient. This uses the actual LongAlpha, not a model. -/
theorem g9_small_third_box_euler_eq_mass (N i j : ℕ) (U V : Finset ℕ) (β : ℕ → ℝ) :
    (∑ m ∈ U, ∑ n ∈ V, fouvryG9LongAlpha N (5 / 4) (i, j, 4) m * β n *
      (∏ p ∈ ({3} : Finset ℕ), (1 - progressionDensity (m * n) p))) =
      ∑ m ∈ U, ∑ n ∈ V, fouvryG9LongAlpha N (5 / 4) (i, j, 4) m * β n := by
  apply sum_congr rfl
  intro m _
  apply sum_congr rfl
  intro n _
  by_cases hm : fouvryG9LongAlpha N (5 / 4) (i, j, 4) m = 0
  · simp [hm]
  obtain ⟨z, hz, he⟩ := g9_longAlpha_ne_zero_labels hm
  have ht := g9_third_box_four_eq_three hz
  have hd : 3 ∣ m := by
    rw [← he, ht]
    exact dvd_mul_left _ _
  have hc : ¬Nat.Coprime 3 (m * n) := by
    intro hc
    exact (Nat.prime_three.coprime_iff_not_dvd.mp hc) (dvd_mul_of_dvd_left hd n)
  simp [progressionDensity_prime _ Nat.prime_three, hc]

/-- Thus the proposed factor at L=8 is strictly too small whenever this
actual third box has positive mass. This is a formal obstruction, not an
unconditional counterexample claiming to instantiate the whole occupied cell. -/
theorem g9_small_third_box_obstruction (N i j : ℕ) (U V : Finset ℕ) (β : ℕ → ℝ)
    (hpos : 0 < ∑ m ∈ U, ∑ n ∈ V,
      fouvryG9LongAlpha N (5 / 4) (i, j, 4) m * β n) :
    ¬ ((∑ m ∈ U, ∑ n ∈ V, fouvryG9LongAlpha N (5 / 4) (i, j, 4) m * β n *
      (∏ p ∈ ({3} : Finset ℕ), (1 - progressionDensity (m * n) p))) ≤
      g9BaseEuler {3} * (1 + 1 / ((8 : ℝ) - 2)) ^ 3 *
        (∑ m ∈ U, ∑ n ∈ V, fouvryG9LongAlpha N (5 / 4) (i, j, 4) m * β n)) := by
  rw [g9_small_third_box_euler_eq_mass]
  norm_num [g9BaseEuler]
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
