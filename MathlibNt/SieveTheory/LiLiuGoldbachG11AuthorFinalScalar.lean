import MathlibNt.SieveTheory.LiLiuGoldbachG11GridKernelPaid
import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorIntegralBound
import MathlibNt.SieveTheory.LiLiuGoldbachG11NormalizedIntegralEnvelope
import MathlibNt.SieveTheory.LiLiuGoldbachWeightG11GoodConsumed

open Finset Filter
open scoped BigOperators Topology
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11AuthorWeight_global_upper (r : ℝ) : goldbachG11AuthorWeight r ≤ 8 := by
  have hm := min_le_right r (1/10 : ℝ)
  unfold goldbachG11AuthorWeight
  apply (div_le_iff₀ (by linarith : 0 < 5*(1-min r (1/10)))).2
  linarith

theorem goldbachG11PrimeKernel_author_add (N : ℕ) (t : ℝ) :
    goldbachG11PrimeKernel (fun r => goldbachG11AuthorWeight r+t) N =
      goldbachG11PrimeKernel goldbachG11AuthorWeight N+t*goldbachG11PrimeKernel (fun _ => 1) N := by
  unfold goldbachG11PrimeKernel
  rw [mul_sum,← sum_add_distrib]
  apply sum_congr rfl
  intro v _
  ring

/-- Pay the already counted ambient-prime-divisor tail on the normalized
mother scale. Reuses the same logarithm/power estimate as the frozen payments. -/
theorem goldbachG11Author_divisor_tail_paid (H d : ℝ) (hd : 0 < d) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      16800*H*Real.log (N : ℝ)/(N : ℝ)^(4/53 : ℝ) ≤ d := by
  have ht : Tendsto (fun x : ℝ => 16800*H*Real.log x/x^(4/53 : ℝ)) atTop (𝓝 0) := by
    have hh := (_root_.isLittleO_log_rpow_rpow_atTop (1 : ℝ) (by norm_num : (0 : ℝ) < 4/53)).tendsto_div_nhds_zero
    simpa only [Real.rpow_one,mul_zero,mul_div_assoc] using (tendsto_const_nhds (x := 16800*H)).mul hh
  obtain ⟨M,hM⟩ := eventually_atTop.mp ((ht.comp tendsto_natCast_atTop_atTop).eventually (gt_mem_nhds hd))
  exact ⟨max 4 M,le_max_left _ _,fun N hN => (hM N ((le_max_right _ _).trans hN)).le⟩

/-- Choose one strictly positive common loss. The three t terms cover the
new divisor tail, actual distribution error, and original G11 exceptional loss. -/
theorem goldbachG11Author_choose_loss (C δ : ℝ) (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 1/8 ∧
      (1+t)^2*((561522/1000000 : ℝ)+t)*
          (goldbachG11PrimeIntegral goldbachG11AuthorWeight+
            (|goldbachG11PrimeIntegral (fun _ => 1)|+2)*t)+9*C*t+3*t <
        (561522/1000000 : ℝ)*goldbachG11PrimeIntegral goldbachG11AuthorWeight+δ := by
  let f : ℝ → ℝ := fun t => (1+t)^2*((561522/1000000 : ℝ)+t)*
    (goldbachG11PrimeIntegral goldbachG11AuthorWeight+(|goldbachG11PrimeIntegral (fun _ => 1)|+2)*t)+9*C*t+3*t
  have hc : ContinuousAt f 0 := by dsimp [f]; fun_prop
  obtain ⟨r,hr,hclose⟩ := Metric.continuousAt_iff.mp hc δ hδ
  let t : ℝ := min (r/2) (1/8)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have ht1 : t ≤ 1/8 := min_le_right _ _
  have htr : t < r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hf := hclose (show dist t 0 < r by simpa [Real.dist_eq,abs_of_pos ht] using htr)
  have hup := (abs_lt.mp (show |f t-f 0| < δ by simpa [Real.dist_eq] using hf)).2
  refine ⟨t,ht,ht1,?_⟩
  dsimp [f] at hup
  nlinarith only [hup]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig