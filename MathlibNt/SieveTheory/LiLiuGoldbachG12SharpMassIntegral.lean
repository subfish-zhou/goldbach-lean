import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpTerminal
import MathlibNt.SieveTheory.LiLiuGoldbachG12SharpQuadrature

noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
/-- Original author sieve weight with both source-certified Buchstab branches. -/
def goldbachG12SharpIntegralConstant : ℝ := goldbachG12PrimeIntegral G12SharpWeight.weight

/-- Actual low mother and ungated high mass, with both approximation losses paid. -/
theorem g12Sharp_authorLowHigh_integral_budget (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℕ, 4 ≤ K ∧ ∀ N ≥ K, ∀ ε : ℝ,
      (Real.log (N : ℝ)/N)*400*(goldbachG12AuthorLowMotherMass N ε+
        8*G12ClippedWindow.highMass N ε) ≤ goldbachG12SharpIntegralConstant+δ := by
  obtain ⟨K,hK,hm⟩ := g12Sharp_authorLowHigh_kernel_terminal (δ/2) (half_pos hδ)
  obtain ⟨L,_,hi⟩ := G12SharpQuadrature.sharp_kernel_le_integral_eventually (δ/2) (half_pos hδ)
  refine ⟨max K L,by omega,?_⟩
  intro N hN ε
  have h := hm N (by omega) ε
  have h' := hi N (by omega)
  unfold goldbachG12SharpIntegralConstant
  linarith only [h,h']
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
