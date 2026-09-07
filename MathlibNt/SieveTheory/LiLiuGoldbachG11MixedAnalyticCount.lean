import MathlibNt.SieveTheory.LiLiuGoldbachG11MixedAnalyticMain

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Both original-count distribution branches and their evaluated arithmetic
main terms. The remaining task is weighted prime-box/Buchstab aggregation. -/
theorem goldbachG11GoodSwitchedTotal_le_analyticMain :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 1 < K ∧ ∀ A : ℕ, ∀ ε ρ δ θ : ℝ,
    0 < ε → ε ≤ 1 → 1 < ρ → ρ ≤ 5/4 →
    0 < δ → δ < 1/4 → 0 < θ → θ < 1/8 →
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
        goldbachG11GridAnalyticMain N ε ρ δ θ C K+5*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨C,hC,K,hK,ha⟩ := goldbachG11MixedDensity_analytic_upper
  refine ⟨C,hC,K,hK,?_⟩
  intro A ε ρ δ θ hε hεu hρ hρu hδ hδu hθ hθu
  obtain ⟨Ma,hMa,ha⟩ := ha δ θ hδ.le hδu hθ hθu
  obtain ⟨Mc,_hMc,hc⟩ := goldbachG11GoodSwitchedTotal_le_mixedDensity A
    hε hεu hρ hρu hδ (by linarith) hθ hθu
  refine ⟨max Ma Mc,hMa.trans (le_max_left _ _),?_⟩
  intro N hN hEven
  obtain ⟨hNa,hNc⟩ := max_le_iff.mp hN
  exact (hc N hNc (Real.sqrt N) (Real.sqrt_nonneg _) (le_refl _)).trans
    (add_le_add (ha N hNa hEven ε ρ hρ hρu) (le_refl _))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig