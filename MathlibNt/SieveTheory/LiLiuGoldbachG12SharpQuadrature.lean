import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpIntegralSplit
import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernelIntegralBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
open MeasureTheory Set Filter
open scoped Interval Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace G12SharpQuadrature

/-- At each fixed point the continuous upper weights eventually equal the sharp weight. -/
theorem upper_eventually_eq (u : ℝ) :
    ∀ᶠ n : ℕ in atTop, upper n u = G12SharpWeight.weight u := by
  by_cases hu : u < 1/10
  · obtain ⟨k, hk⟩ := exists_nat_ge (1 / (1/10 - u))
    filter_upwards [eventually_ge_atTop k] with n hn
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hn
    have hp : 0 < 1/10 - u := sub_pos.mpr hu
    have hprod : 1 ≤ (1/10-u) * n := by
      have hh := (div_le_iff₀ hp).mp (hk.trans hkn)
      nlinarith
    have hz : step n u = 0 := by
      unfold step
      rw [max_eq_left (by nlinarith : 1 + (u-1/10)*(n : ℝ) ≤ 0)]
      norm_num
    rw [upper, hz, sharp_low hu]
    ring
  · exact Eventually.of_forall (fun n => by
      rw [upper, step_high n (le_of_not_gt hu), sharp_high (le_of_not_gt hu)]
      ring)

theorem upper_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => upper n u) atTop (𝓝 (G12SharpWeight.weight u)) :=
  tendsto_const_nhds.congr' (show (fun _ : ℕ => G12SharpWeight.weight u) =ᶠ[atTop]
    (fun n => upper n u) from (upper_eventually_eq u).mono (fun _ h => h.symm))

/-- Dominated convergence is applied only to the exact reduced cross integral. -/
theorem upper_integral_tendsto :
    Tendsto (fun n : ℕ => goldbachG12PrimeIntegral (upper n)) atTop
      (𝓝 (goldbachG12PrimeIntegral G12SharpWeight.weight)) := by
  simp only [integral_eq_density]
  apply Tendsto.const_mul
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun u => 8 * ‖density u‖)
  · exact Eventually.of_forall (fun n =>
      (integrable_weighted (upper n) (continuousOn_upper n)).def'.aestronglyMeasurable)
  · exact Eventually.of_forall (fun n => Eventually.of_forall (fun u _ => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (upper_bounds n u).1]
      exact mul_le_mul_of_nonneg_right (upper_bounds n u).2 (norm_nonneg _)))
  · exact (continuousOn_const.mul continuousOn_density.norm).intervalIntegrable_of_Icc
      (by norm_num)
  · exact Eventually.of_forall (fun u _ => (upper_tendsto u).mul_const (density u))

/-- The original discontinuous sharp author weight on the actual four-prime kernel. -/
theorem sharp_kernel_le_integral_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG12PrimeKernel G12SharpWeight.weight N ≤
        goldbachG12PrimeIntegral G12SharpWeight.weight + δ := by
  have he : ∀ᶠ n : ℕ in atTop, goldbachG12PrimeIntegral (upper n) <
      goldbachG12PrimeIntegral G12SharpWeight.weight + δ/2 :=
    upper_integral_tendsto.eventually (eventually_lt_nhds (by linarith))
  obtain ⟨n, hn⟩ := he.exists
  obtain ⟨N₀, hN₀, hN⟩ := goldbachG12PrimeKernel_le_integral_eventually (upper n)
    (continuousOn_upper n) (fun u _ => (upper_bounds n u).1) (δ/2) (half_pos hδ)
  refine ⟨N₀, hN₀, fun N hNN => ?_⟩
  have hm := kernel_mono G12SharpWeight.weight (upper n) (fun u _ => sharp_le_upper n u)
    (hN₀.trans hNN)
  have hb := hN N hNN
  linarith

/-- Direct one-dimensional low/high consumer, with no numerical bound as an input. -/
theorem sharp_kernel_le_split_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG12PrimeKernel G12SharpWeight.weight N ≤ Real.log (9/4 : ℝ) *
        ((561990/1000000 : ℝ) * (36/5) *
          (∫ u in (4/53 : ℝ)..(1/10), density u / (1-u)) +
        (564383/1000000 : ℝ) * 8 *
          (∫ u in (1/10 : ℝ)..(4/33), density u)) + δ := by
  simpa only [sharp_integral_split] using sharp_kernel_le_integral_eventually δ hδ

end G12SharpQuadrature
