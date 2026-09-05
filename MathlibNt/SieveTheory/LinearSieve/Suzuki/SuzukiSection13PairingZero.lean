import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PQBridge
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingComparison
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The source-faithful κ=1 content of (T5): for each sign, `T̂` is eventually
bounded by a (sign-dependent) constant times `exp (-s)`.  This says decay only;
it does not mention a pairing. -/
def Section13HatExponentialDecay (H : Section13HatLayers) : Prop :=
  ∀ sign, ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ s in atTop, |H.T sign s| ≤ C * Real.exp (-s)

private theorem pairing_tendsto_zero_of_exp_bound
    {R q : ℝ → ℝ} {C K : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hR : ∀ᶠ s in atTop, |R s| ≤ C * Real.exp (-s))
    (hq : ∀ᶠ s in atTop, |q s| ≤ K * s ^ 2)
    (hqwin : ∀ᶠ s in atTop, ∀ t ∈ Ι (s - 1) s, |q (t + 1)| ≤ K * s ^ 2) :
    Tendsto (section10SignedPairing 1 R q) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hrhs : Tendsto (fun s : ℝ =>
      (C * K) * (s ^ 3 * Real.exp (-s) + Real.exp 1 * (s ^ 2 * Real.exp (-s))))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun s : ℝ => Real.exp 1 * (s ^ 2 * Real.exp (-s)))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2) :
          Tendsto (fun s : ℝ => Real.exp 1 * (s ^ 2 * Real.exp (-s))) atTop
            (𝓝 (Real.exp 1 * 0)))
    have hsum := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).add h2
    have hmul : Tendsto (fun s : ℝ => (C * K) *
        (s ^ 3 * Real.exp (-s) + Real.exp 1 * (s ^ 2 * Real.exp (-s))))
        atTop (𝓝 ((C * K) * (0 + 0))) := tendsto_const_nhds.mul hsum
    simpa using hmul
  apply squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _)
    (show ∀ᶠ s in atTop,
      ‖section10SignedPairing 1 R q s‖ ≤
        (C * K) * (s ^ 3 * Real.exp (-s) + Real.exp 1 * (s ^ 2 * Real.exp (-s))) from ?_)
    hrhs
  rcases eventually_atTop.1 hR with ⟨A, hA⟩
  filter_upwards [hq, hqwin, eventually_ge_atTop (max 1 (A + 1))] with s hqs hqw hs
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hs
  have hAs : A + 1 ≤ s := le_trans (le_max_right _ _) hs
  have hs0 : 0 ≤ s := by linarith
  have hab : s - 1 ≤ s := by linarith
  have hint :
      ‖∫ t in s - 1..s, q (t + 1) * R t‖ ≤
        (K * s ^ 2 * (C * Real.exp 1 * Real.exp (-s))) * |s - (s - 1)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have ht' : t ∈ Ioc (s - 1) s := by simpa [uIoc_of_le hab] using ht
    have hRt' : |R t| ≤ C * Real.exp (-t) := hA t (by linarith [ht'.1])
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |q (t + 1)| * |R t| ≤ (K * s ^ 2) * (C * Real.exp (-t)) :=
        mul_le_mul (hqw t ht) hRt' (abs_nonneg _) (mul_nonneg hK (sq_nonneg s))
      _ ≤ (K * s ^ 2) * (C * Real.exp 1 * Real.exp (-s)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (sq_nonneg s))
        calc
          C * Real.exp (-t) ≤ C * (Real.exp 1 * Real.exp (-s)) := by
            apply mul_le_mul_of_nonneg_left _ hC
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by linarith [ht'.1])
          _ = C * Real.exp 1 * Real.exp (-s) := by ring
  rw [show |s - (s - 1)| = 1 by rw [abs_eq_self.mpr] <;> linarith, mul_one] at hint
  simp only [section10SignedPairing, one_mul]
  calc
    ‖s * q s * R s - ∫ t in s - 1..s, q (t + 1) * R t‖ ≤
        ‖s * q s * R s‖ + ‖∫ t in s - 1..s, q (t + 1) * R t‖ := norm_sub_le _ _
    _ ≤ (s * (K * s ^ 2) * (C * Real.exp (-s))) +
        (K * s ^ 2 * (C * Real.exp 1 * Real.exp (-s))) := by
      gcongr
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hs0]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hqs hs0) (hA s (by linarith))
        (abs_nonneg _) (mul_nonneg hs0 (mul_nonneg hK (sq_nonneg s)))
    _ = (C * K) * (s ^ 3 * Real.exp (-s) + Real.exp 1 * (s ^ 2 * Real.exp (-s))) := by ring

end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
