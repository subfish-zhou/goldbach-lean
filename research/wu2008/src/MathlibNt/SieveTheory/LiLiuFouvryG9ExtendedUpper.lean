import MathlibNt.SieveTheory.LiLiuFouvryG9ExtendedUpperEdge
import MathlibNt.SieveTheory.LiLiuPrereqWFExternalSieve

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.G9ExtendedUpper
open Finset ArithmeticFunction SmallRosser
open JurkatRichert1965ChenGammaOneQOne

/-- Upper bound for the actual, unchanged external family on `2 ≤ z ≤ Q²`.
The fixed constant precedes epsilon, and the threshold precedes all density,
carrier, cutoff and dimension data. No lower bound is asserted. -/
theorem exists_externalFamilyDensity_upper_extended :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ Q₀ : ℝ, 4 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
          ∀ ω : ArithmeticFunction ℝ, ω.IsMultiplicative →
            (∀ p ∈ P, 0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
            ∀ z : ℝ, 2 ≤ z → z ≤ Q ^ (2 : ℕ) → (∀ p ∈ P, (p : ℝ) < z) →
              ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
                externalDensity true P (externalInternalLevel Q ε) ε z (primeDensity ω) ≤
                  (∏ p ∈ P, (1 - ω p / (p : ℝ))) *
                    (jr1965F (Real.log Q / Real.log z) +
                      C * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
                        Real.log Q ^ (-(1 / 3 : ℝ)))) := by
  obtain ⟨Co, hCo, ho⟩ := exists_externalFamilyDensity_ff
  obtain ⟨Ce, hCe, he⟩ := exists_signedFamilyDensity_upper_extended
  let C := Co + 2 * Ce
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro ε hε hε8
  obtain ⟨Qo, hQo, ho⟩ := ho ε hε hε8
  obtain ⟨De, hDe, he⟩ := he ε hε hε8
  refine ⟨max Qo (De ^ (1 + ε + ε ^ 9)), hQo.trans (le_max_left _ _), ?_⟩
  intro Q hQ P hP ω hω hg z hz hzQ hcut K hK hdim
  have hQoQ : Qo ≤ Q := (le_max_left _ _).trans hQ
  have hDeQ : De ^ (1 + ε + ε ^ 9) ≤ Q := (le_max_right _ _).trans hQ
  have hQ4 : 4 ≤ Q := hQo.trans hQoQ
  let D := externalInternalLevel Q ε
  let V := ∏ p ∈ P, (1 - ω p / (p : ℝ))
  let T := ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * Real.log Q ^ (-(1 / 3 : ℝ))
  let TD := ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * Real.log D ^ (-(1 / 3 : ℝ))
  have hV : 0 ≤ V := prod_nonneg (fun p hp => sub_nonneg.mpr (hg p hp).2.le)
  have hlogQ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hT : 0 ≤ T := by dsimp [T]; positivity
  change externalDensity true P D ε z (primeDensity ω) ≤
    V * (jr1965F (Real.log Q / Real.log z) + C * T)
  by_cases hzroot : z ≤ Real.sqrt Q
  · have hold := (ho Q hQoQ P hP ω hω hg z hz hzroot hcut K hK hdim).2.2
    change externalDensity true P D ε z (primeDensity ω) ≤
      V * (jr1965F (Real.log Q / Real.log z) + Co * T) at hold
    apply hold.trans
    apply mul_le_mul_of_nonneg_left _ hV
    apply add_le_add_right
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) hT
  · have hD : De ≤ D := externalInternalLevel_ge_threshold (by linarith) hε hε8 hDeQ
    have hD4 : 4 ≤ D := hDe.trans hD
    have hlevel : D ^ (1 + ε + ε ^ 9) = Q :=
      externalInternalLevel_level (by linarith) hε hε8
    have hDleQ : D ≤ Q := by
      rw [← hlevel]
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ D)
          (CoordinateShift.scale_bounds hε hε8).1
    have hzD : Real.sqrt D < z :=
      (Real.sqrt_le_sqrt hDleQ).trans_lt (lt_of_not_ge hzroot)
    have hupper := he D hD P hP ω hω hg K hK hdim z hzD
      (by simpa only [hlevel] using hzQ) hcut
    rw [hlevel] at hupper
    have hTD : TD ≤ 2 * T := externalInternalLevel_error (by linarith) hε hε8
    have hconst : 2 * Ce ≤ C := by dsimp [C]; linarith
    have herror : Ce * TD ≤ C * T := by
      nlinarith only [mul_le_mul_of_nonneg_left hTD hCe.le,
        mul_le_mul_of_nonneg_right hconst hT]
    rw [externalDensity_eq true P hP]
    simp only [not_le.mpr hzD, if_false, if_true]
    change signedFamilyDensity true (externalEdgePrimes P D) D ε
      (geometricSieveLabel D ε) (primeDensity ω) ≤
        V * (jr1965F (Real.log Q / Real.log z) + Ce * TD) at hupper
    exact hupper.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl herror) hV)

#print axioms exists_externalFamilyDensity_upper_extended
end MathlibNt.SieveTheory.LiLiuPrereqWF.G9ExtendedUpper
