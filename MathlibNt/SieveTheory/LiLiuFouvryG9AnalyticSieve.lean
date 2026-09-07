import MathlibNt.SieveTheory.LiLiuFouvryG9MainUpper

noncomputable section
open Finset
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Actual mother upper sieving with the analytic extended F-factor. Both the
prime-density hypotheses and all distribution/transport errors are supplied by
proved producers. The still-visible Euler mass is to be estimated next. -/
theorem fouvryG9Mother_analytic_upper :
    ∃ C : ℝ, 0 < C ∧ ∃ K : ℝ, 1 < K ∧
      ∀ A : ℕ, ∀ e ε δ η ρ : ℝ,
      0 < e → e ≤ 1 → 0 < ε → ε < 4/53 → ε < δ → δ < 1/4 →
      0 < η → η < 1/8 → 1 < ρ → ρ ≤ 5/4 →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → Even N →
      fouvryG9MotherSifted N e (fouvryG9SievePrimes N (Real.sqrt N)) ≤
        (∑ k ∈ fouvryG9GridUsed N e ρ,
          fouvryG9UpperFactor N
            ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))) C K η *
          fouvryG9RectangleEulerMass N ρ k (fouvryG9SievePrimes N (Real.sqrt N))) +
            (N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨C,hC,K,hK,hmain⟩ := fouvryG9RectangleMain_upper
  refine ⟨C,hC,K,hK,?_⟩
  intro A e ε δ η ρ he he1 hε hεa hεδ hδ hη hηu hρ hρu
  obtain ⟨Ns,hs⟩ := fouvryG9MotherSifted_total A he he1 hε hεa hεδ
    (by linarith) hη hηu hρ hρu
  obtain ⟨Nm,hm⟩ := hmain δ η (hε.le.trans hεδ.le) hδ hη hηu
  refine ⟨max Ns Nm,?_⟩
  intro N hN hEven
  have hNs := (le_max_left _ _).trans hN
  have hNm := (le_max_right _ _).trans hN
  apply (hs N hNs (Real.sqrt N)).trans
  apply add_le_add _ le_rfl
  apply sum_le_sum
  intro k hk
  exact (hm N hNm hEven e ρ he hρ hρu k
    (fouvryG9GridCell_nonempty_iff.mpr hk)).2

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
