import MathlibNt.Analysis.LogPowerBounds
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanError

/-!
# Logarithmic payment of beta divisor deletion in the actual signed error

The thresholds precede the changing residue, scales, finite supports and signed
coefficients. All three divisor orders may be zero. The equality progression
is paid separately, without a nondivisibility, SW, Shiu or distribution input.
-/

noncomputable section

open Classical Finset Filter
open scoped Topology

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

theorem betaPayment_eventually_log_mul_rpow_le (K : ℝ) (hK : 0 ≤ K) (B : ℕ)
    {b d : ℝ} (hbd : b < d) :
    ∀ᶠ x : ℝ in atTop, K * (1 + Real.log x) ^ B * x ^ b ≤ x ^ d := by
  exact MathlibNt.Analysis.eventually_log_mul_rpow_le K hK B hbd

/-- Uniformity also covers bounded small integers, not just integers tending
to infinity along with the scale. -/
theorem betaPayment_eventually_tau_le (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, 0 < n → (n : ℝ) ≤ 2 * x →
      (fouvryTau k n : ℝ) ≤ x ^ δ := by
  obtain ⟨C, hC, hbound⟩ :=
    fouvryTau_le_const_rpow (k := k + 1) (by omega)
      (show 0 < δ / 2 by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show 0 < δ / 2 by linarith)).eventually_ge_atTop
      (C * (2 : ℝ) ^ (δ / 2))] with x hx hconst
  intro n hn hnx
  have hx0 : 0 < x := by linarith
  calc
    _ ≤ (fouvryTau (k + 1) n : ℝ) := by exact_mod_cast fouvryTau_le_succ k n
    _ ≤ C * (n : ℝ) ^ (δ / 2) := hbound n hn
    _ ≤ C * (2 * x) ^ (δ / 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hnx (by linarith)) hC.le
    _ = (C * (2 : ℝ) ^ (δ / 2)) * x ^ (δ / 2) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0.le, mul_assoc]
    _ ≤ x ^ (δ / 2) * x ^ (δ / 2) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hx0.le _)
    _ = x ^ δ := by rw [← Real.rpow_add hx0]; congr 1; ring

/-- A finite cardinality estimate for arbitrary, possibly sparse, dyadic
alpha supports. -/
theorem betaPayment_card_dyadic_le {M : ℝ} (hM : 1 ≤ M) (S : Finset ℕ)
    (hS : ∀ m ∈ S, M ≤ (m : ℝ) ∧ (m : ℝ) ≤ 2 * M) :
    (S.card : ℝ) ≤ 2 * M := by
  have hsub : S ⊆ Ioc 0 ⌊2 * M⌋₊ := by
    intro m hm
    apply mem_Ioc.mpr
    refine ⟨?_, Nat.le_floor (hS m hm).2⟩
    have : (0 : ℝ) < m := by have := (hS m hm).1; linarith
    exact_mod_cast this
  have hcard := card_le_card hsub
  simp only [Nat.card_Ioc, Nat.sub_zero] at hcard
  exact (show (S.card : ℝ) ≤ (⌊2 * M⌋₊ : ℝ) by exact_mod_cast hcard).trans
    (Nat.floor_le (by linarith))


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
