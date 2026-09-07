import MathlibNt.SieveTheory.LiLiuGoldbachWeightSifted
import MathlibNt.SieveTheory.LiLiuGoldbachB10ProductCount
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachWeightProduct (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Exact product-indexed source, with actual coefficients and moving q fibres. -/
noncomputable def goldbachWeightTwelveProductRHS
    (A : Finset ℕ) (N : ℕ) (ε z b c T Z : ℝ) : ℤ :=
  goldbachWeightTwelveBase A N z b c T -
    ∑ m ∈ goldbachC10ProductSupport N b c,
      (goldbachC10Coeff N b c m : ℤ) *
        (((goldbachB10ProductQFiber N ε m).filter
          (fun q => literalHPoint N 1 Z (N - m * q))).card : ℤ)

theorem goldbachWeight_twelve_product_log_scale_eventually
    (ε δ θ : ℝ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) (hδ : 0 < δ)
    (_hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∀ α β γ Z : ℝ,
      (1 : ℝ) / 18 < α → α < β → β < (1 - 3 * β) / 3 →
      (1 - 3 * β) / 3 < γ → γ < (1 : ℝ) / 3 →
      1 ≤ Z → Z ≤ (N : ℝ) ^ θ →
      (goldbachWeightTwelveProductRHS (goldbachDifferenceCarrier N ε) N ε
        ((N : ℝ) ^ α) ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
        ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) Z : ℝ) -
        δ * (N : ℝ) / (Real.log N) ^ 2 ≤ 4 * (D19 N : ℝ) := by
  simpa only [goldbachWeightTwelveProductRHS, goldbachWeightTwelveSiftedRHS,
    goldbachB10SiftedCount_eq_sum_productSupport] using
    goldbachWeight_twelve_sifted_log_scale_eventually ε δ θ hε hεu hδ _hθ0 hθ1

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig