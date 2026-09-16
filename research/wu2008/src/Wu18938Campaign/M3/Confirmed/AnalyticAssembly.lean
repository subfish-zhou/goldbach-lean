import Wu18938Campaign.M3.Confirmed.FifthClassical

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Real Wu2008DoubleSieve Wu08TerminalAlignment SingleUpperCounts

def analyticClassicalLedger : ℝ := conservativeLedger-14/1000000

theorem analytic_classical_ledger_exact :
    analyticClassicalLedger = (179813583/200000000:ℝ) := by
  norm_num [analyticClassicalLedger,conservativeLedger,originalNumericLedger,correctedG2]

theorem analytic_classical_ledger_margin :
    analyticClassicalLedger-(899/1000:ℝ) = 13583/200000000 ∧
      (899/1000:ℝ) < analyticClassicalLedger := by
  rw [analytic_classical_ledger_exact]
  norm_num

theorem coefficient_lower_from_three_classical_inputs
    (hC1 : (14900897/1000000:ℝ) ≤ firstMain)
    (hC3 : thirdMain ≤ (23652925/1000000:ℝ))
    (hC4 : fourthMain ≤ (19643510/1000000:ℝ)) :
    analyticClassicalLedger ≤ paidOriginalCoefficient := by
  have h5 := FifthClassical.fifth_main_lower
  have h7 := SeventhNinth.seventh_main_upper
  have h8 := Eighth.eighth_main_upper
  have h9 := SeventhNinth.ninth_main_upper
  unfold analyticClassicalLedger conservativeLedger originalNumericLedger paidOriginalCoefficient
  linarith only [hC1,hC3,hC4,h5,h7,h8,h9]

variable
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

include hnodes h34 h5 h6 hC1 hC3 hC4

theorem ordinary_analytic_count_from_remaining_inputs {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (analyticClassicalLedger-ε)*truncatedSixthMassScale N ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨T,hT,h⟩ := ordinary_count_from_remaining_improvements hnodes h34 h5 h6 he
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  exact (mul_le_mul_of_nonneg_right
    (sub_le_sub_right (coefficient_lower_from_three_classical_inputs hC1 hC3 hC4) ε)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (h N hN hEven)

theorem ordinary_899_from_remaining_inputs {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((899/1000:ℝ)-ε)*truncatedSixthMassScale N ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨T,hT,h⟩ :=
    ordinary_analytic_count_from_remaining_inputs hnodes h34 h5 h6 hC1 hC3 hC4 he
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  exact (mul_le_mul_of_nonneg_right
    (sub_le_sub_right analytic_classical_ledger_margin.2.le ε)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (h N hN hEven)

theorem refined_1894_from_remaining_inputs :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthMassScale N/400 <
        ((Wu2004MeanValue.refinedGood N (947/500)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r:ℝ) ≤ (q:ℝ)^(447/500:ℝ) :=
  refined_1894_from_ordinary_count
    (fun _ he => ordinary_899_from_remaining_inputs hnodes h34 h5 h6 hC1 hC3 hC4 he)

end Wu18938Campaign.M3.Confirmed
