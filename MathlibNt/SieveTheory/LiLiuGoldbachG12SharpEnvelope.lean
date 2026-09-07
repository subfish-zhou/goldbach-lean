import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpWeight
import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernel
noncomputable section
namespace G12SharpQuadrature
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Integer steepness keeps the transition strictly to the left of the junction. -/
def step (n : ℕ) (u : ℝ) : ℝ := min 1 (max 0 (1 + (u - 1/10) * n))
def upper (n : ℕ) (u : ℝ) : ℝ :=
  (561990/1000000 + (564383/1000000 - 561990/1000000) * step n u) *
    goldbachG11AuthorWeight u

theorem step_bounds (n : ℕ) (u : ℝ) : 0 ≤ step n u ∧ step n u ≤ 1 :=
  ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩

theorem step_high (n : ℕ) {u : ℝ} (hu : 1/10 ≤ u) : step n u = 1 := by
  unfold step
  apply min_eq_left
  exact le_trans (show (1 : ℝ) ≤ 1 + (u - 1/10) * n by
    nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]) (le_max_right _ _)

theorem upper_bounds (n : ℕ) (u : ℝ) : 0 ≤ upper n u ∧ upper n u ≤ 8 := by
  have hs := step_bounds n u
  have hw := goldbachG11AuthorWeight_nonneg u
  have hw' := goldbachG12AuthorWeight_le_eight u
  have hf : 0 ≤ (561990/1000000 : ℝ) + (564383/1000000 - 561990/1000000) * step n u ∧
      (561990/1000000 : ℝ) + (564383/1000000 - 561990/1000000) * step n u ≤ 1 := by
    constructor <;> nlinarith [hs.1, hs.2]
  exact ⟨mul_nonneg hf.1 hw, (mul_le_mul hf.2 hw' hw zero_le_one).trans_eq (one_mul 8)⟩

theorem sharp_le_upper (n : ℕ) (u : ℝ) : G12SharpWeight.weight u ≤ upper n u := by
  apply mul_le_mul_of_nonneg_right _ (goldbachG11AuthorWeight_nonneg u)
  unfold G12SharpWeight.factor
  split_ifs with hu
  · have hs := (step_bounds n u).1
    nlinarith
  · rw [step_high n (le_of_not_gt hu)]
    norm_num

theorem continuousOn_upper (n : ℕ) :
    ContinuousOn (upper n) (Set.Icc (4/53 : ℝ) (4/33)) := by
  apply ContinuousOn.mul _ continuousOn_goldbachG11AuthorWeight
  exact (by unfold step; fun_prop : Continuous (fun u : ℝ =>
    561990/1000000 + (564383/1000000 - 561990/1000000) * step n u)).continuousOn

/-- All original labels, including repeated primes and endpoints, are retained. -/
theorem kernel_mono (h g : ℝ → ℝ)
    (hh : ∀ u ∈ Set.Icc (4/53 : ℝ) (4/33), h u ≤ g u) {N : ℕ} (hN : 4 ≤ N) :
    goldbachG12PrimeKernel h N ≤ goldbachG12PrimeKernel g N := by
  apply Finset.sum_le_sum
  intro v hv
  have hg := goldbachG12PrimeKernel_logGeometry hN hv
  apply div_le_div_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg _) hg.2.le)
  exact mul_le_mul_of_nonneg_right (hh _ hg.1)
    (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega)))

end G12SharpQuadrature
