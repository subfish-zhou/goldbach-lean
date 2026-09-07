import MathlibNt.SieveTheory.LiLiuFouvryG9ProductFibre

open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The literal short prime/coprimality coefficient obeys the one-fold divisor bound. -/
theorem fouvryG9_prime_copN_beta_bounds (N n : ℕ) :
    0 ≤ (if n.Coprime N then primeSWBeta n else 0) ∧
    (if n.Coprime N then primeSWBeta n else 0) ≤ (fouvryTau 1 n : ℝ) := by
  classical
  by_cases hc : n.Coprime N
  · simp only [if_pos hc]
    by_cases hp : n.Prime
    · simp [primeSWBeta, hp, fouvryTau, ArithmeticFunction.zeta_apply, hp.ne_zero]
    · simp [primeSWBeta, hp]
  · simp [hc]

/-- The actual long multiplicity and literal prime/copN short coefficient,
with an arbitrary finite rectangle and no additional geometric assumptions. -/
theorem fouvryG9Long_prime_product_fibre_le
    (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (U V : Finset ℕ) (v : ℕ) :
    (∑ p ∈ U ×ˢ V, if p.1 * p.2 = v then
      fouvryG9LongAlpha N ρ k p.1 * (if p.2.Coprime N then primeSWBeta p.2 else 0)
      else 0) ≤ (fouvryTau 3 v : ℝ) := by
  apply fouvryG9_weighted_product_fibre_le U V (fouvryG9LongAlpha N ρ k)
    (fun n => if n.Coprime N then primeSWBeta n else 0) v
  · intro m _
    obtain ⟨h0, hle, heq⟩ := fouvryG9LongAlpha_bounds N ρ k m
    exact ⟨h0, heq ▸ hle⟩
  · intro n _
    exact fouvryG9_prime_copN_beta_bounds N n

/-- The genuine absolute-difference bound for the same source coefficients. -/
theorem fouvryG9Long_prime_natAbs_fibre_le
    (N : ℕ) (ρ : ℝ) (k : ℕ × ℕ × ℕ) (U V : Finset ℕ) (r : ℕ) :
    (∑ p ∈ U ×ˢ V, if ((N : ℤ) - (p.1 : ℤ) * p.2).natAbs = r then
      fouvryG9LongAlpha N ρ k p.1 * (if p.2.Coprime N then primeSWBeta p.2 else 0)
      else 0) ≤ (fouvryTau 3 (N + r) : ℝ) + (fouvryTau 3 (N - r) : ℝ) := by
  apply fouvryG9_weighted_natAbs_fibre_le U V (fouvryG9LongAlpha N ρ k)
    (fun n => if n.Coprime N then primeSWBeta n else 0) N r
  · intro m _
    obtain ⟨h0, hle, heq⟩ := fouvryG9LongAlpha_bounds N ρ k m
    exact ⟨h0, heq ▸ hle⟩
  · intro n _
    exact fouvryG9_prime_copN_beta_bounds N n

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
