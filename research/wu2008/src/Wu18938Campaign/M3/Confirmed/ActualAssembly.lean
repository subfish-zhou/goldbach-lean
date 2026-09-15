import Wu18938Campaign.M3.Confirmed.SecondConsumers
import Wu18938Campaign.M3.Confirmed.NegativeCounts

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Real Wu2008DoubleSieve Wu08TerminalAlignment
open SingleUpperCounts TruncatedElevenSignedLower TruncatedElevenClassicalCountLower

def paidOriginalCoefficient : ℝ :=
  (3*firstMain+(9103015/1000000+correctedG2)-thirdMain-fourthMain+
    39890/1000000+8860/1000000+fifthMain+1359/1000000+
    3879092/1000000-2*seventhMain-eighthMain-ninthMain-851/1250)/4

theorem paid_original_coefficient_lower
    (hC1 : (14900897/1000000:ℝ) ≤ firstMain)
    (hC3 : thirdMain ≤ (23652925/1000000:ℝ))
    (hC4 : fourthMain ≤ (19643510/1000000:ℝ))
    (hC5 : (1654808/1000000:ℝ) ≤ fifthMain)
    (hC7 : seventhMain ≤ (585179/1000000:ℝ))
    (hC8 : eighthMain ≤ (5279581/1000000:ℝ))
    (hC9 : ninthMain ≤ (5372410/1000000:ℝ)) :
    conservativeLedger ≤ paidOriginalCoefficient := by
  unfold conservativeLedger originalNumericLedger paidOriginalCoefficient
  linarith only [hC1,hC3,hC4,hC5,hC7,hC8,hC9]

theorem ordinary_count_from_remaining_improvements
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
    {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (paidOriginalCoefficient-ε)*truncatedSixthMassScale N ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  have he10 : 0 < ε/10 := by positivity
  obtain ⟨T1,_,h1⟩ := first_actual_count he10
  obtain ⟨T2,_,h2⟩ := numericG2_eventual_second_count hnodes he10
  obtain ⟨T34,_,hu⟩ := h34 (ε/10) he10
  obtain ⟨T5,_,hp⟩ := h5 (ε/10) he10
  obtain ⟨T6,_,hk⟩ := h6 (ε/10) he10
  obtain ⟨T78,hT78,h78⟩ := original_seventh_eighth_actual_upper he10
  obtain ⟨T9,_,h9⟩ := original_ninth_upper he10
  obtain ⟨Tq,_,hq⟩ := original_four_actual_upper he10
  obtain ⟨Te,_,herr⟩ := exceptional_power_error_paid he10
  obtain ⟨Tz,_,hz⟩ := fixed_cutoff_eventually_admissible
  refine ⟨max T1 (max T2 (max T34 (max T5 (max T6
    (max T78 (max T9 (max Tq (max Te Tz)))))))),by omega,fun N hN hEven => ?_⟩
  have hN4 : 4 ≤ N := by omega
  have h1N := h1 N (by omega) hEven
  have h2N := h2 N (by omega) hEven
  have huN := hu N (by omega) hEven
  have hpN := hp N (by omega) hEven
  have hkN := hk N (by omega) hEven
  have h78N := h78 N (by omega) hEven
  have h9N := h9 N (by omega) hEven
  have hqN := hq N (by omega) hEven
  have heN := herr N (by omega)
  have hm := fixedPaperMother_actual_count hN4 hEven (hz N (by omega))
  change _ ≤ 4*((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) at hm
  rw [fixedPaperMother_eq, fixed_expression_literal] at hm
  change (TruncatedFourPhysical.Q10 N : ℝ)+(TruncatedFourPhysical.Q11 N : ℝ) ≤ _ at hqN
  unfold TruncatedFourPhysical.Q10 TruncatedFourPhysical.Q11
    TruncatedFourPhysical.T10 TruncatedFourPhysical.T11 fourModulusProduct at hqN
  have hscale := truncatedSixthClosure_scale_nonneg hN4
  have hslack : 0 ≤ ε*truncatedSixthMassScale N := mul_nonneg he.le hscale
  unfold paidOriginalCoefficient
  change _ ≤ (ninthMain+ε/10)*wuSingularSeries N*N/log N^(2:ℕ) at h9N
  unfold truncatedSixthMassScale at h2N huN hpN hkN h78N hqN hslack ⊢
  ring_nf at h1N h2N huN hpN hkN h78N h9N hqN heN hm hslack ⊢
  linarith only [h1N,h2N,huN,hpN,hkN,h78N,h9N,hqN,heN,hm,hslack]

theorem refined_1894_from_remaining_improvements
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
    (hC5 : (1654808/1000000:ℝ) ≤ fifthMain)
    (hC7 : seventhMain ≤ (585179/1000000:ℝ))
    (hC8 : eighthMain ≤ (5279581/1000000:ℝ))
    (hC9 : ninthMain ≤ (5372410/1000000:ℝ)) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthMassScale N/400 <
        ((Wu2004MeanValue.refinedGood N (947/500)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r:ℝ) ≤ (q:ℝ)^(447/500:ℝ) := by
  apply refined_1894_from_conservative_count
  intro ε he
  obtain ⟨T,hT,hc⟩ := ordinary_count_from_remaining_improvements hnodes h34 h5 h6 he
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  exact (mul_le_mul_of_nonneg_right
    (sub_le_sub_right (paid_original_coefficient_lower hC1 hC3 hC4 hC5 hC7 hC8 hC9) ε)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (hc N hN hEven)

end Wu18938Campaign.M3.Confirmed
