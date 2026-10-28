import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySmallDelta
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform logarithmic payment of the small-gcd zero-mode difference

Siegel--Walfisz is a hypothesis on a given family, not a property asserted
for arbitrary beta. Its constant is chosen before the family member and all
AP moduli, coprime sieves, and residues. The threshold below is likewise
chosen before the member, scales, supports, and signed modulus weights.
The large-gcd term remains outside these estimates.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset Filter
open scoped Topology

noncomputable section

/-- The family-uniform, independently coprime-sieved beta-SW input.
The sieve order is fixed; the saving exponent and its constant precede
every changing family member and every arithmetic parameter. -/
def BetaCoprimeSWFamily {ι : Type*} (κ : ℕ) (T : ι → ℝ)
    (N : ι → Finset ℕ) (β : ι → ℕ → ℝ) : Prop :=
  ∀ B : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ i : ι, ∀ d h : ℕ, 0 < d → 0 < h → ∀ b : ℕ, b.Coprime d →
      |betaCoprimeAPDiscrepancy (N i) (β i) d h b| ≤
        C * T i * (fouvryTau κ h : ℝ) / Real.log (2 * T i) ^ B

/-- Passing from the lower dyadic scale to the upper support endpoint does
not strengthen the SW input: its constant grows by the fixed factor `2^B`. -/
theorem BetaCoprimeSWFamily.double_scale
    {ι : Type*} {κ : ℕ} {T : ι → ℝ}
    {N : ι → Finset ℕ} {β : ι → ℕ → ℝ}
    (hSW : BetaCoprimeSWFamily κ T N β) (hT : ∀ i, 1 ≤ T i) :
    BetaCoprimeSWFamily κ (fun i => 2 * T i) N β := by
  intro B
  obtain ⟨C, hC, hAP⟩ := hSW B
  refine ⟨C * 2 ^ B, by positivity, ?_⟩
  intro i d h hd hh b hb
  have ht : 0 < T i := lt_of_lt_of_le zero_lt_one (hT i)
  have hl : 0 < Real.log (2 * T i) := Real.log_pos (by linarith [hT i])
  have hl' : 0 < Real.log (2 * (2 * T i)) := Real.log_pos (by linarith [hT i])
  have hlog : Real.log (2 * (2 * T i)) ≤ 2 * Real.log (2 * T i) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : 2 * T i ≠ 0)]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (show 2 ≤ 2 * T i by linarith [hT i])
    linarith
  have hp := pow_le_pow_left₀ hl'.le hlog B
  rw [mul_pow] at hp
  apply (hAP i d h hd hh b hb).trans
  apply (div_le_div_iff₀ (pow_pos hl B) (pow_pos hl' B)).mpr
  calc
    _ ≤ (C * T i * (fouvryTau κ h : ℝ)) * (2 ^ B * Real.log (2 * T i) ^ B) :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ _ := by
      have hn : 0 ≤ C * T i * (fouvryTau κ h : ℝ) *
          (2 ^ B * Real.log (2 * T i) ^ B) := by positivity
      nlinarith


/-- Elementary logarithm accounting at `T ≥ x^ε`. The saving order is
explicitly the desired order plus the beta/modulus/delta logarithm costs. -/
theorem smallDelta_log_budget (p s d A : ℕ)
    {x T L D ε : ℝ} (hx : 1 ≤ Real.log x) (hx0 : 0 < x)
    (hT : 1 ≤ T) (hL : 1 ≤ L) (hTx : T ≤ x) (hLx : L ≤ x)
    (hε : 0 < ε) (hεT : x ^ ε ≤ T) (hD : 0 ≤ D)
    (hDx : D ≤ Real.log x ^ d) :
    (1 + Real.log T) ^ p * D * (1 + Real.log L) ^ s /
        Real.log (2 * T) ^ (A + (p + s + d)) ≤
      (2 : ℝ) ^ (p + s) / ε ^ (A + (p + s + d)) / Real.log x ^ A := by
  have hlogx : 0 < Real.log x := by linarith
  have hlogT := Real.log_nonneg hT
  have hlogL := Real.log_nonneg hL
  have hHT : 1 + Real.log T ≤ 2 * Real.log x := by
    have := Real.log_le_log (by linarith : 0 < T) hTx
    linarith
  have hHL : 1 + Real.log L ≤ 2 * Real.log x := by
    have := Real.log_le_log (by linarith : 0 < L) hLx
    linarith
  have hden : ε * Real.log x ≤ Real.log (2 * T) := by
    have h₁ := Real.log_le_log (Real.rpow_pos_of_pos hx0 ε) hεT
    rw [Real.log_rpow hx0] at h₁
    have h₂ := Real.log_le_log (by linarith : 0 < T) (show T ≤ 2 * T by linarith)
    linarith
  have hden0 : 0 < Real.log (2 * T) := Real.log_pos (by linarith)
  calc
    _ ≤ (2 * Real.log x) ^ p * Real.log x ^ d * (2 * Real.log x) ^ s /
        (ε * Real.log x) ^ (A + (p + s + d)) := by
      apply div_le_div₀
      · positivity
      · gcongr
      · positivity
      · exact pow_le_pow_left₀ (by positivity) hden _
    _ = _ := by
      simp only [mul_pow, pow_add]
      field_simp


end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
