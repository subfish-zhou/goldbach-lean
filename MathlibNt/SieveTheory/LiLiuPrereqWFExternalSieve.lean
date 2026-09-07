import MathlibNt.SieveTheory.LiLiuPrereqWFExternalPrimeDensity
import MathlibNt.SieveTheory.LiLiuPrereqWFEdgeDensity

/-!
# The common well-factorable linear sieve at the prescribed external level

The same explicit families cover the full domain 2 <= z <= sqrt Q. All
constants and thresholds precede the density data and the original K.
The zero lower edge uses the proved O(epsilon) bound for the genuine f;
the truncated upper edge uses its own proved Euler-normalized density.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction SmallRosser
open JurkatRichert1965ChenGammaOneQOne

theorem exists_externalFamilyDensity_ff :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ Q₀ : ℝ, 4 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
          ∀ ω : ArithmeticFunction ℝ, ω.IsMultiplicative →
            (∀ p ∈ P, 0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
            ∀ z : ℝ, 2 ≤ z → z ≤ Real.sqrt Q → (∀ p ∈ P, (p : ℝ) < z) →
              ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
                let D := externalInternalLevel Q ε
                let V := ∏ p ∈ P, (1 - ω p / (p : ℝ))
                let E := C * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
                  Real.log Q ^ (-(1 / 3 : ℝ)))
                4 ≤ D ∧
                  V * (jr1965f (Real.log Q / Real.log z) - E) ≤
                    externalDensity false P D ε z (primeDensity ω) ∧
                  externalDensity true P D ε z (primeDensity ω) ≤
                    V * (jr1965F (Real.log Q / Real.log z) + E) := by
  obtain ⟨Ci, hCi, hi⟩ := exists_signedFamilyDensity_ff
  obtain ⟨Ce, hCe, he⟩ := EdgeDensity.exists_signedFamilyDensity_upper_edge
  obtain ⟨Cs, hCs, hs⟩ := CoordinateShift.exists_uniform_coordinate_shift
  let A := jr1965DelayConstant
  have hA : 0 < A := CoordinateShift.delayConstant_pos
  let C := 2 * Ci + Cs + 2 * Ce + 2 * A
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε hε8
  obtain ⟨Di, hDi, hi⟩ := hi ε hε hε8
  obtain ⟨De, hDe, he⟩ := he ε hε hε8
  let D₀ := max Di De
  have hD₀ : 4 ≤ D₀ := hDe.trans (le_max_right _ _)
  have hc : 1 ≤ 1 + ε + ε ^ 9 := (external_dilation_bounds hε hε8).1.le
  have hD₀Q : D₀ ≤ D₀ ^ (1 + ε + ε ^ 9) := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ D₀) hc
  refine ⟨D₀ ^ (1 + ε + ε ^ 9), hD₀.trans hD₀Q, ?_⟩
  intro Q hQ P hP ω hω hg z hz hzQ hcut K hK hdim
  let D := externalInternalLevel Q ε
  have hD : D₀ ≤ D := externalInternalLevel_ge_threshold (by linarith) hε hε8 hQ
  have hD4 : 4 ≤ D := hD₀.trans hD
  have hDiD : Di ≤ D := (le_max_left _ _).trans hD
  have hDeD : De ≤ D := (le_max_right _ _).trans hD
  have hQ4 : 4 ≤ Q := hD₀.trans (hD₀Q.trans hQ)
  have hlevel : D ^ (1 + ε + ε ^ 9) = Q :=
    externalInternalLevel_level (by linarith) hε hε8
  let V := ∏ p ∈ P, (1 - ω p / (p : ℝ))
  let T := ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * Real.log Q ^ (-(1 / 3 : ℝ))
  let TD := ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) * Real.log D ^ (-(1 / 3 : ℝ))
  have hV : 0 ≤ V := prod_nonneg (fun p hp => sub_nonneg.mpr (hg p hp).2.le)
  have htail : 0 ≤ (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
      Real.log Q ^ (-(1 / 3 : ℝ)) :=
    mul_nonneg (by positivity) (Real.rpow_nonneg (Real.log_pos (by linarith)).le _)
  have hT : 0 ≤ T := add_nonneg hε.le htail
  have hεT : ε ≤ T := le_add_of_nonneg_right htail
  have hTD : TD ≤ 2 * T := externalInternalLevel_error (by linarith) hε hε8
  have hCiC : 2 * Ci + Cs ≤ C := by dsimp [C]; linarith
  have hCeC : 2 * Ce ≤ C := by dsimp [C]; linarith
  have hAC : 2 * A ≤ C := by dsimp [C]; linarith
  change 4 ≤ D ∧
    V * (jr1965f (Real.log Q / Real.log z) - C * T) ≤
      externalDensity false P D ε z (primeDensity ω) ∧
    externalDensity true P D ε z (primeDensity ω) ≤
      V * (jr1965F (Real.log Q / Real.log z) + C * T)
  refine ⟨hD4, ?_⟩
  rw [externalDensity_eq false P hP, externalDensity_eq true P hP]
  by_cases hzD : z ≤ Real.sqrt D
  · simp only [hzD, if_true]
    have hden := hi D hDiD P hP ω hω hg z hz hzD
      (fun p hp => hcut p (mem_sdiff.mp hp).1) K hK hdim
    have hshift := hs ε hε hε8 (Real.log D / Real.log z)
      (sieve_coordinate_ge_two (by linarith) hz hzD)
    have hcoord : Real.log Q / Real.log z =
        (1 + ε + ε ^ 9) * (Real.log D / Real.log z) :=
      externalInternalLevel_coordinate (by linarith) hε hε8
    rw [← hcoord] at hshift
    have herror : Ci * TD + Cs * ε ≤ C * T := by
      nlinarith only [mul_le_mul_of_nonneg_left hTD hCi.le,
        mul_le_mul_of_nonneg_left hεT hCs.le,
        mul_le_mul_of_nonneg_right hCiC hT]
    have hpay := mul_le_mul_of_nonneg_left herror hV
    have hfl := mul_le_mul_of_nonneg_left hshift.2 hV
    have hfu := mul_le_mul_of_nonneg_left hshift.1 hV
    change V * (jr1965f (Real.log D / Real.log z) - Ci * TD) ≤ _ ∧
      _ ≤ V * (jr1965F (Real.log D / Real.log z) + Ci * TD) at hden
    constructor
    · nlinarith only [hden.1, hpay, hfl]
    · nlinarith only [hden.2, hpay, hfu]
  · simp only [hzD, if_false, Bool.false_eq_true, if_true]
    have hedge : Real.sqrt D < z := lt_of_not_ge hzD
    have hcoord := external_edge_coordinate (by linarith : 1 < Q) hε hε8 hz hzQ hedge
    have hlow := CoordinateShift.lower_edge_le hε hε8 hcoord.1 hcoord.2.le
    change jr1965f (Real.log Q / Real.log z) ≤ 2 * A * ε at hlow
    have hlowpay : jr1965f (Real.log Q / Real.log z) ≤ C * T := by
      nlinarith only [hlow, mul_le_mul_of_nonneg_left hεT (by positivity : 0 ≤ 2 * A),
        mul_le_mul_of_nonneg_right hAC hT]
    refine ⟨mul_nonpos_of_nonneg_of_nonpos hV (sub_nonpos.mpr hlowpay), ?_⟩
    have hupper := he D hDeD P hP ω hω hg K hK hdim z hedge
      (by simpa only [hlevel] using hzQ) hcut
    rw [hlevel] at hupper
    change signedFamilyDensity true (externalEdgePrimes P D) D ε
      (geometricSieveLabel D ε) (primeDensity ω) ≤
        V * (jr1965F (Real.log Q / Real.log z) + Ce * TD) at hupper
    have herror : Ce * TD ≤ C * T := by
      nlinarith only [mul_le_mul_of_nonneg_left hTD hCe.le,
        mul_le_mul_of_nonneg_right hCeC hT]
    exact hupper.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl herror) hV)

/-- One fixed, constructed family, its genuine F/f main terms, original
signed divisor remainders, source cardinality and all real level splits. -/
theorem exists_external_sieve_common_family {ι : Type*} :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ Q₀ : ℝ, 4 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
          ∀ ω : ArithmeticFunction ℝ, ω.IsMultiplicative →
            (∀ p ∈ P, 0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
            ∀ z : ℝ, 2 ≤ z → z ≤ Real.sqrt Q → (∀ p ∈ P, (p : ℝ) < z) →
              ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
                let D := externalInternalLevel Q ε
                let V := ∏ p ∈ P, (1 - ω p / (p : ℝ))
                let E := C * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
                  Real.log Q ^ (-(1 / 3 : ℝ)))
                (∀ upper : Bool,
                  ((externalTags upper P D ε z).card : ℝ) < Real.exp (8 * (ε⁻¹) ^ 3) ∧
                    ∀ t ∈ externalTags upper P D ε z,
                      WellFactorable (externalTerm upper P D ε z t) Q) ∧
                  ∀ (I : Finset ι) (a : ι → ℕ) (X : ℝ), 0 ≤ X →
                    X * V * (jr1965f (Real.log Q / Real.log z) - E) +
                        externalRemainder false P D ε z I a X (primeDensity ω) ≤
                      sequenceSifted I a P ∧
                    sequenceSifted I a P ≤
                      X * V * (jr1965F (Real.log Q / Real.log z) + E) +
                        externalRemainder true P D ε z I a X (primeDensity ω) := by
  obtain ⟨C, hC, hmain⟩ := exists_externalFamilyDensity_ff
  refine ⟨C, hC, ?_⟩
  intro ε hε hε8
  obtain ⟨Q₀, hQ₀, hmain⟩ := hmain ε hε hε8
  refine ⟨Q₀, hQ₀, ?_⟩
  intro Q hQ P hP ω hω hg z hz hzQ hcut K hK hdim
  obtain ⟨hD, hl, hu⟩ := hmain Q hQ P hP ω hω hg z hz hzQ hcut K hK hdim
  dsimp only at hD hl hu ⊢
  have hlevel := externalInternalLevel_level
    (show 0 ≤ Q by linarith) hε hε8
  constructor
  · intro upper
    simpa only [hlevel] using externalTags_card_and_wellFactorable upper P z
      (by linarith : 2 ≤ externalInternalLevel Q ε) hε hε8
  · intro I a X hX
    have hsieve := externalFamily_sequence_sieve P hP
      (show 2 ≤ externalInternalLevel Q ε by linarith) hε hε8 hcut
      I a X (primeDensity ω)
    have hlo := mul_le_mul_of_nonneg_left hl hX
    have hup := mul_le_mul_of_nonneg_left hu hX
    constructor
    · nlinarith only [hsieve.1, hlo]
    · nlinarith only [hsieve.2, hup]

#check exists_externalFamilyDensity_ff
#print axioms exists_externalFamilyDensity_ff
#check exists_external_sieve_common_family
#print axioms exists_external_sieve_common_family

end MathlibNt.SieveTheory.LiLiuPrereqWF
