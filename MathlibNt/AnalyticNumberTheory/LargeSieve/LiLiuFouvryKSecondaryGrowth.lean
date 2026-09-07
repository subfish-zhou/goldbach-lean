import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectPaySecondaryUniform

/-! Fixed-scale shift growth, with the constant chosen before varying data. -/
noncomputable section
open Classical Finset
namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The divisor constant depends only on delta; the scale loss is explicit. -/
theorem directPayKSecondary_tau {δ : ℝ} (hδ : 0 < δ) :
    ∃ Ca : ℝ, 0 < Ca ∧ ∀ (Cscale : ℝ), 1 ≤ Cscale →
      ∀ (x : ℝ), 1 ≤ x → ∀ a : ℤ, |(a : ℝ)| ≤ Cscale * x →
        (a.natAbs.divisors.card : ℝ) ≤ Ca * Cscale ^ δ * x ^ δ := by
  obtain ⟨Ca, hCa, ht⟩ := directPaySecondary_tau hδ
  refine ⟨Ca, hCa, ?_⟩
  intro Cscale hscale x hx a ha
  have hs0 : 0 ≤ Cscale := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hsx : 1 ≤ Cscale * x := hx.trans (le_mul_of_one_le_left hx0 hscale)
  have hh := ht (Cscale * x) hsx a ha
  rw [Real.mul_rpow hs0 hx0] at hh
  simpa only [mul_assoc] using hh

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
