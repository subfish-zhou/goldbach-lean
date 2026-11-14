module

public import MathlibNt.SieveTheory.LiLiuPrereqWFEdgeDensityScalar
public import MathlibNt.SieveTheory.LiLiuPrereqWFCoordinateShift
import MathlibNt.SieveTheory.LiLiuFouvryG9ExtendedUpperEdge

/-!
# Genuine upper density at the external near-two edge

The family is the accepted upper family on primes strictly below `sqrt D`.
For large dimension constants its bounded aggregate replaces, rather than
inflates, the internal analytic estimate.
-/

@[expose] public section

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.EdgeDensity

open Finset ArithmeticFunction SmallRosser
open JurkatRichert1965ChenGammaOneQOne
open scoped Classical

/-- The absolute constant is chosen before epsilon; the threshold precedes
the prime carrier, multiplicative density, original dimension constant and
external cutoff. The weights are exactly the already accepted family. -/
theorem exists_signedFamilyDensity_upper_edge :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 4 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
          ∀ ω : ArithmeticFunction ℝ, ω.IsMultiplicative →
            (∀ p ∈ P, 0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
            ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
              ∀ z : ℝ, Real.sqrt D < z →
                z ≤ Real.sqrt (D ^ (1 + ε + ε ^ 9)) →
                (∀ p ∈ P, (p : ℝ) < z) →
                signedFamilyDensity true (P.filter (fun p : ℕ => (p : ℝ) < Real.sqrt D))
                    D ε (geometricSieveLabel D ε) (primeDensity ω) ≤
                  (∏ p ∈ P, (1 - ω p / (p : ℝ))) *
                    (jr1965F (Real.log (D ^ (1 + ε + ε ^ 9)) / Real.log z) +
                      C * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
                        Real.log D ^ (-(1 / 3 : ℝ)))) := by
  obtain ⟨C, hC, hbound⟩ := G9ExtendedUpper.exists_signedFamilyDensity_upper_extended
  refine ⟨C, hC, fun ε hε hε8 => ?_⟩
  obtain ⟨D₀, hD₀, hbound⟩ := hbound ε hε hε8
  refine ⟨D₀, hD₀, fun D hD P hP ω hω hg K hK hdim z hz hzQ hcut => ?_⟩
  have hD1 : 1 ≤ D := by linarith
  have hscale : 1 ≤ D ^ (1 + ε + ε ^ 9) := Real.one_le_rpow hD1 (by positivity)
  have hcutoff := (Real.sqrt_le_self_iff.mpr (Or.inr hscale)).trans
    (le_self_pow₀ hscale (by decide : (2 : ℕ) ≠ 0))
  exact hbound D hD P hP ω hω hg K hK hdim z hz (hzQ.trans hcutoff) hcut

end MathlibNt.SieveTheory.LiLiuPrereqWF.EdgeDensity
