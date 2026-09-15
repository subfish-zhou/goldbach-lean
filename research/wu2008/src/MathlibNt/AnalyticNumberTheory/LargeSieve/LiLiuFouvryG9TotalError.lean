import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9GridCost
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuFouvryG9RectangleC2

noncomputable section
open Finset
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Total absolute distribution error of the genuine positive G9 rectangular
majorant. Every cell may use its own original-level well-factorable weight.
There is no assumed per-cell error estimate: expanded C2 supplies it. -/
theorem fouvryG9RectangleError_total (j A : ℕ) {e ε δ ρ : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) (hε : 0 < ε) (hεa : ε < 4/53)
    (hεδ : ε < δ) (hδ : δ ≤ 1/2) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ c : (ℕ × ℕ × ℕ) → ℕ → ℝ,
      (∀ k ∈ fouvryG9GridUsed N e ρ,
        SignedWellFactorable j
          ((N : ℝ)^(5/9-δ)/(((2/3 : ℝ)*ρ^k.1)^(5/9 : ℝ))) (c k)) →
      ∑ k ∈ fouvryG9GridUsed N e ρ, |fouvryG9RectangleError N ρ δ k (c k)| ≤
        (N : ℝ)/Real.log (N : ℝ)^A := by
  have hK : 1 ≤ 2/e := (le_div_iff₀ he).2 (by linarith)
  obtain ⟨N₁,hcells⟩ := fouvryG9RectangleError_uniform j (A+4) he he1 hε hεa hεδ hδ
  obtain ⟨N₂,hcost⟩ := fouvryG9GridCost_total ρ (2/e) A hρ hK
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN c hc
  apply hcost N ((le_max_right _ _).trans hN) e
    (fun k => 4*ρ^(k.2.1+k.2.2)*((2/3 : ℝ)*ρ^k.1))
    (fun k => fouvryG9RectangleError N ρ δ k (c k))
  · intro k hk
    have hne := fouvryG9GridCell_nonempty_iff.mpr hk
    obtain ⟨_,hxlo,hxhi,_,_⟩ := fouvryG9Grid_buffered_geometry he hρ hρu hne
    exact ⟨hxlo,hxhi⟩
  · intro k hk
    exact hcells N ((le_max_left _ _).trans hN) ρ hρ hρu k
      (fouvryG9GridCell_nonempty_iff.mpr hk) (c k) (hc k hk)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
