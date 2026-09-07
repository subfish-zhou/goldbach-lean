import MathlibNt.SieveTheory.LiLiuPrereqWFFamilyDensity
import MathlibNt.SieveTheory.LiLiuPrereqWFTagCardinalityExp
import MathlibNt.SieveTheory.LiLiuPrereqWFSignedRemainder

/-!
# The common well-factorable sieve on the internal level domain

The explicitly defined family is independent of the sequence and of every
factorization. Its actual cardinality, order-one well-factorability, genuine
F/f main terms, and actual signed remainders occur together below.

The range is `z ≤ sqrt D`, while the weight level is
`Q = D^(1+epsilon+epsilon^9)`. This is not the missing extension to
`z ≤ sqrt Q`. The remainder here is restricted to primorial divisors;
full-modulus use still requires the previously proved transport and its costs.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction SmallRosser
open JurkatRichert1965ChenGammaOneQOne

/-- A constructed, bounded-size, common WF family with its own analytic
density and finite sieve bounds. Repeated values and zero sequence entries
are allowed; no distribution estimate is assumed. -/
theorem exists_internal_sieve_common_family {ι : Type*} :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 8 →
      ∃ D₀ : ℝ, 2 ≤ D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
        ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime) →
          ∀ ω : ArithmeticFunction ℝ, ω.IsMultiplicative →
            (∀ p ∈ P, 0 ≤ ω p / (p : ℝ) ∧ ω p / (p : ℝ) < 1) →
            ∀ z : ℝ, 2 ≤ z → z ≤ Real.sqrt D →
              (∀ p ∈ P, (p : ℝ) < z) →
              ∀ K : ℝ, 0 ≤ K → DimensionOneProductBound P (primeDensity ω) K →
                let label := geometricSieveLabel D ε
                let V := ∏ p ∈ P, (1 - ω p / (p : ℝ))
                let E := C * (ε + (ε ^ 8)⁻¹ * Real.exp (6 * K + 2) *
                  Real.log D ^ (-(1 / 3 : ℝ)))
                (∀ upper : Bool,
                  ((signedTags upper P D ε label).card : ℝ) < Real.exp (8 * (ε⁻¹) ^ 3) ∧
                    ∀ t ∈ signedTags upper P D ε label,
                      WellFactorable (signedFamilyTerm upper P D ε t)
                        (D ^ (1 + ε + ε ^ 9))) ∧
                ∀ (I : Finset ι) (a : ι → ℕ) (X : ℝ), 0 ≤ X →
                  X * V * (jr1965f (Real.log D / Real.log z) - E) +
                      signedFamilyRemainder false P D ε label I a X (primeDensity ω) ≤
                        sequenceSifted I a P ∧
                    sequenceSifted I a P ≤
                      X * V * (jr1965F (Real.log D / Real.log z) + E) +
                        signedFamilyRemainder true P D ε label I a X (primeDensity ω) := by
  obtain ⟨C, hC, hmain⟩ := exists_signedFamilyDensity_ff
  refine ⟨C, hC, ?_⟩
  intro ε hε hεsmall
  obtain ⟨D₀, hD₀, hmain⟩ := hmain ε hε hεsmall
  refine ⟨D₀, hD₀, ?_⟩
  intro D hD P hP ω hω hg z hz hzD hcut K hK hdim
  have hD2 : 2 ≤ D := hD₀.trans hD
  have hrough : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < z :=
    fun p hp => hcut p (mem_sdiff.mp hp).1
  have hmain := hmain D hD P hP ω hω hg z hz hzD hrough K hK hdim
  dsimp only at hmain ⊢
  constructor
  · intro upper
    exact ⟨signedTags_card_lt_exp_source upper P _ hD2 hε hεsmall,
      signedTags_common_wellFactorable upper P _ hD2 hε hεsmall⟩
  · intro I a X hX
    have hsieve := signedFamily_sequence_sieve P hP hD2 hε hεsmall
      (fun p hp => (hrough p hp).trans_le hzD) I a X (primeDensity ω)
    have hl := mul_le_mul_of_nonneg_left hmain.1 hX
    have hu := mul_le_mul_of_nonneg_left hmain.2 hX
    dsimp only at hsieve
    constructor <;> nlinarith [hsieve.1, hsieve.2]

#check exists_internal_sieve_common_family
#print axioms exists_internal_sieve_common_family

end MathlibNt.SieveTheory.LiLiuPrereqWF
