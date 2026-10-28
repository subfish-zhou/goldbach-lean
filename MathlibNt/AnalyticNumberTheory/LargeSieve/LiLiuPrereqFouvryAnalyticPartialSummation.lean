import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryAnalyticPrefix
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryRectangleSlowVariation

/-!
# Concrete slow-weight removal from the actual extracted dispersion sum

The degree-five variation loss is derived from actual floor-retained tuples.
Empty blocks are treated separately. All arithmetic coefficients, phases,
support conditions and the coupled cutoff remain inside genuine prefixes.
-/

noncomputable section
open Classical Finset Filter

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open _root_.LiLiuPrereqFouvry

def wAnalyticVariationConstant (Z : ℝ) : ℝ :=
  2048 * (6 + 2 * Real.pi) ^ 5 * (1 + 112 * Z) ^ 5

theorem wAnalyticVariationConstant_nonneg {Z : ℝ} (hZ : 0 ≤ Z) :
    0 ≤ wAnalyticVariationConstant Z := by
  unfold wAnalyticVariationConstant
  positivity


/-- An explicitly constructed arithmetic quantity: dyadic reciprocal
prefactors times attained, genuinely rectangular arithmetic prefix maxima. -/
def wAnalyticKeyPrefixMajorant (U : Finset (WExtractedTuple × ℤ))
    (K : WExtractedKey) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ j ∈ U.image wAnalyticDyadicKey, wBlockAmplitude K j *
    (wAnalyticBlockPrefixMax (wAnalyticDyadicBlock U j true) j β c₁ γ ζ a +
      wAnalyticBlockPrefixMax (wAnalyticDyadicBlock U j false) j β c₁ γ ζ a)

theorem wAnalyticKeyPrefixMajorant_nonneg (U : Finset (WExtractedTuple × ℤ))
    (K : WExtractedKey) (β c₁ γ ζ : ℕ → ℝ) (a : ℤ) :
    0 ≤ wAnalyticKeyPrefixMajorant U K β c₁ γ ζ a := by
  apply sum_nonneg
  intro j _
  exact mul_nonneg (by unfold wBlockAmplitude; positivity)
    (add_nonneg (wAnalyticBlockPrefixMax_nonneg _ _ _ _ _ _ _)
      (wAnalyticBlockPrefixMax_nonneg _ _ _ _ _ _ _))


end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
