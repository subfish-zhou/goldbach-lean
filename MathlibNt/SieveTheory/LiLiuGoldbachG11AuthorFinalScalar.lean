import Mathlib.Topology.Order.LeftRight
import MathlibNt.SieveTheory.LiLiuGoldbachG11GridKernelPaid
import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorIntegralBound
import MathlibNt.SieveTheory.LiLiuGoldbachG11NormalizedIntegralEnvelope

open Finset Filter
open scoped BigOperators Topology
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


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
  have he := hc.eventually (gt_mem_nhds (lt_add_of_pos_right (f 0) hδ))
  obtain ⟨t,ht,ht1,hf⟩ := ((eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/8)).and he).exists_gt
  refine ⟨t,ht,ht1.le,?_⟩
  simpa [f] using hf

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig