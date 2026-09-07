import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCoprimePartitionLogarithmic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Subpolynomial cost at the F87 prime-factor cutoff

The partition count is at most `x^ε`, uniformly for `2 ≤ T ≤ x` and
`ω ≤ C*(log x)^(1/5)`, for any fixed positive `C`. In particular `C = 2`
includes the product-variable cutoff used in F87, Section III.7, p. 628.
-/

open Filter Asymptotics
open scoped Topology

namespace LiLiuPrereqFouvry.CoprimePartition

theorem partition_cost_isLittleO :
    (fun u : ℝ => u ^ (2 / 5 : ℝ) * Real.log (partitionConstant * u)) =o[atTop]
      (fun u : ℝ => u) := by
  have hconst :
      (fun _ : ℝ => Real.log partitionConstant) =o[atTop]
        (fun u : ℝ => u ^ (3 / 5 : ℝ)) :=
    (isLittleO_const_id_atTop (Real.log partitionConstant)).comp_tendsto
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5))
  have hlog := hconst.add (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 5))
  have hmul := (isBigO_refl (fun u : ℝ => u ^ (2 / 5 : ℝ)) atTop).mul_isLittleO hlog
  refine hmul.congr' ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    simp only [Real.log_mul partitionConstant_pos.ne' hu.ne']
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with u hu
    rw [← Real.rpow_add hu]
    norm_num

theorem eventually_partition_log_cost {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (2 / 5 : ℝ) * Real.log (partitionConstant * Real.log x) ≤
        ε * Real.log x := by
  have h := Real.tendsto_log_atTop.eventually (partition_cost_isLittleO.bound hε)
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx₁
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx₁
  exact (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, abs_of_nonneg hlog] using hx)

/-- The asymptotic cost is uniform both in the real cutoff and in the growing number
of distinct prime factors. No fixed-`ω` assumption is used. -/
theorem eventually_card_realPartition_le_rpow_of_factor
    {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ T : ℝ, 2 ≤ T → T ≤ x → ∀ ω : ℕ,
      (ω : ℝ) ≤ C * Real.log x ^ (1 / 5 : ℝ) →
        ((realPartition T ω).card : ℝ) ≤ x ^ ε := by
  filter_upwards [eventually_partition_log_cost
    (show 0 < ε / C ^ 2 by positivity), eventually_ge_atTop (2 : ℝ)] with x hx hx₂
  intro T hT hTx ω hω
  have hx₀ : 0 < x := by linarith
  have hT₀ : 0 < T := by linarith
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog₂ : Real.log 2 ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx₂
  have hbase : 1 ≤ partitionConstant * Real.log x := by
    have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hc : partitionConstant * Real.log 2 = 4 := by
      simp [partitionConstant, htwo.ne']
    have hm := mul_le_mul_of_nonneg_left hlog₂ partitionConstant_pos.le
    linarith
  have hω₂ : ((ω ^ 2 : ℕ) : ℝ) ≤ C ^ 2 * Real.log x ^ (2 / 5 : ℝ) := by
    have hs := pow_le_pow_left₀ (Nat.cast_nonneg ω) hω 2
    have heq : (Real.log x ^ (1 / 5 : ℝ)) ^ (2 : ℕ) =
        Real.log x ^ (2 / 5 : ℝ) := by
      rw [← Real.rpow_mul_natCast hlogx]
      norm_num
    simpa only [Nat.cast_pow, mul_pow, heq] using hs
  have hlogbase : 0 ≤ Real.log (partitionConstant * Real.log x) := Real.log_nonneg hbase
  have hpay : C ^ 2 *
      (Real.log x ^ (2 / 5 : ℝ) * Real.log (partitionConstant * Real.log x)) ≤
        ε * Real.log x := by
    apply (mul_le_mul_of_nonneg_left hx (sq_nonneg C)).trans_eq
    field_simp
  have hexponent :
      Real.log (partitionConstant * Real.log x) * ((ω ^ 2 : ℕ) : ℝ) ≤
        Real.log x * ε := by
    have hm := mul_le_mul_of_nonneg_right hω₂ hlogbase
    nlinarith
  calc
    ((realPartition T ω).card : ℝ) ≤ (partitionConstant * Real.log T) ^ (ω ^ 2) :=
      card_realPartition_le_log hT ω
    _ ≤ (partitionConstant * Real.log x) ^ (ω ^ 2) :=
      pow_le_pow_left₀
        (mul_nonneg partitionConstant_pos.le (Real.log_nonneg (by linarith)))
        (mul_le_mul_of_nonneg_left (Real.log_le_log hT₀ hTx) partitionConstant_pos.le) _
    _ = Real.exp (Real.log (partitionConstant * Real.log x) * ((ω ^ 2 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
    _ ≤ Real.exp (Real.log x * ε) := Real.exp_le_exp.mpr hexponent
    _ = x ^ ε := (Real.rpow_def_of_pos hx₀ ε).symm

theorem eventually_card_realPartition_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ T : ℝ, 2 ≤ T → T ≤ x → ∀ ω : ℕ,
      (ω : ℝ) ≤ Real.log x ^ (1 / 5 : ℝ) →
        ((realPartition T ω).card : ℝ) ≤ x ^ ε := by
  simpa only [one_mul] using
    eventually_card_realPartition_le_rpow_of_factor (C := 1) zero_lt_one hε

end LiLiuPrereqFouvry.CoprimePartition
