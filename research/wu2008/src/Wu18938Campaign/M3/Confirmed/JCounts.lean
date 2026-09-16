import Wu18938Campaign.M3.Confirmed.Eighth

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Real Wu2008DoubleSieve Wu08TerminalAlignment
open SingleUpperCounts TruncatedElevenSignedLower

theorem numeric_seventh_eighth_actual_upper {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      2*(lowerS2 N ((N:ℝ)^truncatedSixthLowerBeta)
        ((N:ℝ)^truncatedSixthLowerSigma) : ℝ) +
        (lowerS3 N ((N:ℝ)^truncatedSixthLowerAlpha) ((N:ℝ)^(1/3:ℝ)) : ℝ) ≤
      ((6449939/1000000:ℝ)+ε)*truncatedSixthMassScale N := by
  obtain ⟨T,hT,h⟩ := original_seventh_eighth_actual_upper he
  refine ⟨T,hT,fun N hN hEven => (h N hN hEven).trans ?_⟩
  apply mul_le_mul_of_nonneg_right _ (truncatedSixthClosure_scale_nonneg (by omega))
  linarith only [SeventhNinth.seventh_main_upper,Eighth.eighth_main_upper]

theorem numeric_ninth_actual_upper {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (variableS3Main N ((N:ℝ)^truncatedSixthLowerBeta)
        ((N:ℝ)^truncatedSixthLowerSigma) : ℝ) ≤
      ((5372410/1000000:ℝ)+ε)*truncatedSixthMassScale N := by
  obtain ⟨T,hT,h⟩ := original_ninth_upper he
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  have hn := h N hN hEven
  change _ ≤ (ninthMain+ε)*wuSingularSeries N*N/log N^(2:ℕ) at hn
  have hscale := truncatedSixthClosure_scale_nonneg (show 4 ≤ N by omega)
  have hm := mul_le_mul_of_nonneg_right
    (add_le_add_right SeventhNinth.ninth_main_upper ε) hscale
  unfold truncatedSixthMassScale at hm ⊢
  ring_nf at hn hm ⊢
  linarith only [hn,hm]

theorem coefficient_lower_from_four_classical_inputs
    (hC1 : (14900897/1000000:ℝ) ≤ firstMain)
    (hC3 : thirdMain ≤ (23652925/1000000:ℝ))
    (hC4 : fourthMain ≤ (19643510/1000000:ℝ))
    (hC5 : (1654808/1000000:ℝ) ≤ fifthMain) :
    conservativeLedger ≤ paidOriginalCoefficient :=
  paid_original_coefficient_lower hC1 hC3 hC4 hC5
    SeventhNinth.seventh_main_upper Eighth.eighth_main_upper SeventhNinth.ninth_main_upper

theorem refined_1894_from_four_classical_inputs
    (hnodes : ∀ η : ℝ, 0 < η →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1/100 →
        (6440/10000000:ℝ)-η ≤ wuImprovementLimit false δ (21/5) ∧
        (52233/10000000:ℝ)-η ≤ wuImprovementLimit true δ (16/5))
    (h34 : ∀ ε : ℝ, 0 < ε →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (U N (1/3) : ℝ)+(U N truncatedSixthLowerSigma : ℝ) ≤
          (thirdMain+fourthMain-39890/1000000-8860/1000000+ε)*
            truncatedSixthMassScale N)
    (h5 : ∀ ε : ℝ, 0 < ε →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        (fifthMain+1359/1000000-ε)*truncatedSixthMassScale N ≤ (fifthPairCount N : ℝ))
    (h6 : ∀ ε : ℝ, 0 < ε →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
        ((3879092/1000000:ℝ)-ε)*truncatedSixthMassScale N ≤
          (truncatedSixthMass N ((N:ℝ)^truncatedSixthLowerAlpha)
            ((N:ℝ)^truncatedSixthLowerBeta) ((N:ℝ)^truncatedSixthLowerSigma)
            ((N:ℝ)^truncatedSixthLowerLambda) : ℝ))
    (hC1 : (14900897/1000000:ℝ) ≤ firstMain)
    (hC3 : thirdMain ≤ (23652925/1000000:ℝ))
    (hC4 : fourthMain ≤ (19643510/1000000:ℝ))
    (hC5 : (1654808/1000000:ℝ) ≤ fifthMain) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthMassScale N/400 <
        ((Wu2004MeanValue.refinedGood N (947/500)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r:ℝ) ≤ (q:ℝ)^(447/500:ℝ) :=
  refined_1894_from_remaining_improvements hnodes h34 h5 h6 hC1 hC3 hC4 hC5
    SeventhNinth.seventh_main_upper Eighth.eighth_main_upper SeventhNinth.ninth_main_upper

end Wu18938Campaign.M3.Confirmed
