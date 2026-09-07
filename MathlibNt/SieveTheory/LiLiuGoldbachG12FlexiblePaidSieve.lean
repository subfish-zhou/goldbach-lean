import MathlibNt.SieveTheory.LiLiuGoldbachG12FlexibleCorrectionBudget
noncomputable section
open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
namespace G12FlexibleWF

/-- Actual arbitrary-endpoint output sieve with both full-carrier corrections
replaced by proved quantitative budgets; the original full C2 sums remain. -/
theorem exists_rectangle_paid_sieve :
    ∃ K C : ℝ, 1 < K ∧ 0 < C ∧ ∀ η : ℝ, 0 < η → η < 1/8 →
      ∃ Q₀ : ℝ, 4 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
        ∀ (N : ℕ) (_hN : 2 ≤ N) (_hEven : Even N) (ε Z : ℝ) (M U T V : ℕ),
          (N : ℝ)^(4/53 : ℝ) ≤ T → (V : ℝ) < (N : ℝ)^(1/10 : ℝ) →
          2 ≤ Z → Z ≤ Real.sqrt Q → Q ≤ N → 2 ≤ externalInternalLevel Q η →
          let A := G12FlexibleRectangle.rectangle N ε M U T V
          let P := goldbachB10SiftingPrimes N Z
          let D := externalInternalLevel Q η
          let Euler := ∏ p ∈ P, (1 - AnalyticNumberTheory.Sieve.goldbachNu p)
          let E := C * (η + (η^8)⁻¹ * Real.exp (6*K+2) * Real.log Q^(-(1/3 : ℝ)))
          (∀ t ∈ externalTags true P D η Z,
            WellFactorable (externalTerm true P D η Z t) Q ∧
            SignedWellFactorable 1 Q (fun d => externalTerm true P D η Z t d)) ∧
          (400 * ∑ p ∈ A,
            goldbachG12NormalizedCoefficient N p.1 * (if (N-p.2*p.1).Prime then 1 else 0)) ≤
            400 * mass N A * Euler * (jr1965F (Real.log Q / Real.log Z) + E) +
            400 * (∑ t ∈ externalTags true P D η Z,
              |G12FlexibleRectangle.discrepancy N A (Ioc 0 ⌊Q⌋₊)
                (externalTerm true P D η Z t)|) +
            400*((externalTags true P D η Z).card : ℝ)*correctionBudget N Q η +
            8000*(Nat.ceil Z : ℝ) := by
  obtain ⟨K,C,hK,hC,hs⟩ := exists_rectangle_full_sieve
  refine ⟨K,C,hK,hC,?_⟩
  intro η hη hηu
  obtain ⟨Q₀,hQ₀,hs⟩ := hs η hη hηu
  refine ⟨Q₀,hQ₀,?_⟩
  intro Q hQ N hN hEven ε Z M U T V hlo hhi hZ hZQ hQN hD
  obtain ⟨hf,hu⟩ := hs Q hQ N hN hEven ε Z M U T V hlo hhi hZ hZQ
  dsimp only at hf hu ⊢
  refine ⟨hf,?_⟩
  have hp := signed_corrections_paid hN ε _
    (rectangle_image_subset N ε M U T V hlo hhi) Z Q η hQN hD hη hηu
    (fun t ht => (hf t ht).1)
  have hh := mul_le_mul_of_nonneg_left hp (show (0 : ℝ) ≤ 400 by norm_num)
  dsimp only at hh
  linarith only [hu,hh]

end G12FlexibleWF
