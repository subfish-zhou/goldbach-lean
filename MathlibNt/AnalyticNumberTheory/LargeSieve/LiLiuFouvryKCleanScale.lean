import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanPayment
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanSW

noncomputable section
open Filter
open scoped Topology
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Only the auxiliary SW scale is enlarged; the physical scale is unchanged. -/
theorem kClean_aux_scale_rpow_le {Cscale x ε : ℝ}
    (hC : 1 ≤ Cscale) (hx : Cscale ≤ x) (hε : 0 < ε) :
    (Cscale * x) ^ (ε / 2) ≤ x ^ ε := by
  have hx0 : 0 ≤ x := by linarith
  calc
    _ ≤ (x * x) ^ (ε / 2) := Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_right hx hx0) (by positivity)
    _ = x ^ ε := by
      rw [Real.mul_rpow hx0 hx0, ← Real.rpow_add (by linarith : 0 < x)]
      congr 1
      ring

/-- Fixed multiplicative ranges cost only a uniform threshold. -/
theorem kClean_eventually_tau_le (k : ℕ) {Cscale δ : ℝ}
    (hC : 1 ≤ Cscale) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Cscale * x →
      (fouvryTau k n : ℝ) ≤ x ^ δ := by
  obtain ⟨C, hC0, hbound⟩ :=
    fouvryTau_le_const_rpow (k := k + 1) (by omega)
      (show 0 < δ / 2 by linarith)
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop (show 0 < δ / 2 by linarith)).eventually_ge_atTop
      (C * Cscale ^ (δ / 2))] with x hx hconst
  intro n hn hnx
  have hx0 : 0 < x := by linarith
  calc
    _ ≤ (fouvryTau (k + 1) n : ℝ) := by exact_mod_cast fouvryTau_le_succ k n
    _ ≤ C * (n : ℝ) ^ (δ / 2) := hbound n hn
    _ ≤ C * (Cscale * x) ^ (δ / 2) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) hnx (by linarith)) hC0.le
    _ = (C * Cscale ^ (δ / 2)) * x ^ (δ / 2) := by
      rw [Real.mul_rpow (by linarith : 0 ≤ Cscale) hx0.le, mul_assoc]
    _ ≤ x ^ (δ / 2) * x ^ (δ / 2) :=
      mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hx0.le _)
    _ = x ^ δ := by rw [← Real.rpow_add hx0]; congr 1; ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
