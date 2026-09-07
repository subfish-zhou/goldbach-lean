import MathlibNt.SieveTheory.LiLiuGoldbachG11AuthorFactorPaid
import MathlibNt.SieveTheory.LiLiuGoldbachG11MixedAnalyticCount

open Finset
open scoped BigOperators Classical
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Literal expanded prime-box mass with the original product multiplicity
and a weight on the actual short-prime logarithmic coordinate. -/
def goldbachG11WeightedGridMass (N : ℕ) (ε ρ : ℝ) (h : ℝ → ℝ) : ℝ :=
  ∑ k ∈ goldbachG11GridUsed N ε ρ,
    ∑ v ∈ goldbachG11GridLong N ε ρ k ×ˢ goldbachG11GridShort N ρ k,
      goldbachG11AllPrimeWeight N v*h (Real.log (v.2 : ℝ)/Real.log (N : ℝ))

/-- Actual good G11 count with the author's weight. All distribution, sieve,
level, Euler and small-output errors are supplied internally. The remaining
expanded-box-to-original-Buchstab comparison is deliberately visible. -/
theorem goldbachG11GoodSwitchedTotal_le_authorGrid (τ : ℝ) (hτ : 0 < τ)
    (A : ℕ) {ε ρ : ℝ} (hε : 0 < ε) (hεu : ε ≤ 1) (hρ : 1 < ρ) (hρu : ρ ≤ 5/4) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachG11GoodSwitchedTotal N ε ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) : ℝ) ≤
      (SingularSeries.liuSingularSeries N/Real.log (N : ℝ))*
        goldbachG11WeightedGridMass N ε ρ (fun r => goldbachG11AuthorWeight r+τ)+
        5*(N : ℝ)/Real.log (N : ℝ)^A := by
  obtain ⟨C,hC,K,_hK,hcount⟩ := goldbachG11GoodSwitchedTotal_le_analyticMain
  obtain ⟨δ₀,hδ₀,hδu,θ₀,hθ₀,hθu,hfactor⟩ := goldbachG11AuthorFactor_paid C K τ hC.le hτ
  let δ := δ₀/2
  let θ := θ₀/2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδs : δ < δ₀ := by dsimp [δ]; linarith
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθs : θ < θ₀ := by dsimp [θ]; linarith
  obtain ⟨Mf,hMf,hf⟩ := hfactor δ θ hδ.le hδs hθ hθs
  obtain ⟨Mc,_hMc,hc⟩ := hcount A ε ρ δ θ hε hεu hρ hρu hδ (hδs.trans hδu) hθ (hθs.trans hθu)
  refine ⟨max Mf Mc,hMf.trans (le_max_left _ _),?_⟩
  intro N hN hEven
  obtain ⟨hNf,hNc⟩ := max_le_iff.mp hN
  have hm : goldbachG11GridAnalyticMain N ε ρ δ θ C K ≤
      (SingularSeries.liuSingularSeries N/Real.log (N : ℝ))*
        goldbachG11WeightedGridMass N ε ρ (fun r => goldbachG11AuthorWeight r+τ) := by
    unfold goldbachG11GridAnalyticMain goldbachG11GridPlainMass goldbachG11WeightedGridMass
    simp only [mul_sum]
    apply sum_le_sum
    intro k hk
    apply sum_le_sum
    intro v hv
    have hh := hf N hNf hEven ε ρ hρ hρu k hk v.2 (mem_product.mp hv).2
    have hmul := mul_le_mul_of_nonneg_right hh (goldbachG11AllPrimeWeight_nonneg N v)
    exact hmul.trans_eq (by ring)
  exact (hc N hNc hEven).trans (add_le_add hm (le_refl _))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig