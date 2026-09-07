import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectCoefficients
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryBetaCleanPayment

noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Actual outer alpha square sum, including divisor order zero, uniformly in support. -/
theorem direct_alpha_mass_subpower (i : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x M : ℝ), 1 ≤ x → 1 ≤ M → 2*M ≤ x →
      ∀ (U : Finset ℕ) (α : ℕ → ℝ),
      (∀ n ∈ U, M ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2*M) →
      (∀ n ∈ U, |α n| ≤ (fouvryTau i n : ℝ)) →
      (∑ n ∈ U, α n^2) ≤ C*M*x^δ := by
  obtain ⟨B, hB, hb⟩ := direct_tau_subpower i (show 0 < δ/2 by positivity)
  refine ⟨2*B^2, by positivity, ?_⟩
  intro x M hx hM hMx U α hU hα
  have hx0 : 0 < x := by linarith
  have he : 0 ≤ B*x^(δ/2) := by positivity
  have hc := betaPayment_card_dyadic_le hM U hU
  calc
    _ ≤ ∑ _n ∈ U, (B*x^(δ/2))^2 := by
      apply sum_le_sum
      intro n hn
      have h := (hα n hn).trans (hb x hx n ((hU n hn).2.trans hMx))
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (α n)) h 2
    _ = (U.card : ℝ)*(B*x^(δ/2))^2 := by simp
    _ ≤ (2*M)*(B*x^(δ/2))^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = (2*B^2)*M*x^δ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hx0.le]
      norm_num
      ring

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
