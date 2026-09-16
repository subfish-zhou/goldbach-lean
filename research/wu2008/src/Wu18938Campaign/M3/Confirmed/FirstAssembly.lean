import Wu18938Campaign.M3.Confirmed.FirstClassical

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Real Wu2008DoubleSieve Wu08TerminalAlignment SingleUpperCounts

def firstPaidLedger : ℝ := analyticClassicalLedger-3/4000000

theorem first_paid_ledger_margin :
    firstPaidLedger = (179813433/200000000:ℝ) ∧
      (899/1000:ℝ) < firstPaidLedger := by
  rw [firstPaidLedger,analytic_classical_ledger_exact]
  norm_num

theorem coefficient_lower_from_two_classical_inputs
    (hC3 : thirdMain ≤ (23652925/1000000:ℝ))
    (hC4 : fourthMain ≤ (19643510/1000000:ℝ)) :
    firstPaidLedger ≤ paidOriginalCoefficient := by
  have h1 := FirstClassical.first_main_lower
  have h5 := FifthClassical.fifth_main_lower
  have h7 := SeventhNinth.seventh_main_upper
  have h8 := Eighth.eighth_main_upper
  have h9 := SeventhNinth.ninth_main_upper
  unfold firstPaidLedger analyticClassicalLedger conservativeLedger
    originalNumericLedger paidOriginalCoefficient
  linarith only [h1,hC3,hC4,h5,h7,h8,h9]

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
    (hC3 : thirdMain ≤ (23652925/1000000:ℝ))
    (hC4 : fourthMain ≤ (19643510/1000000:ℝ))

include hnodes h34 h5 h6 hC3 hC4

theorem ordinary_899_with_paid_first {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((899/1000:ℝ)-ε)*truncatedSixthMassScale N ≤
        ((MathlibNt.Wu2008DoubleSieve.wuPrimeComplements N).card : ℝ) := by
  obtain ⟨T,hT,h⟩ := ordinary_count_from_remaining_improvements hnodes h34 h5 h6 he
  have hc := first_paid_ledger_margin.2.le.trans
    (coefficient_lower_from_two_classical_inputs hC3 hC4)
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_right hc ε)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (h N hN hEven)

theorem refined_1894_with_paid_first :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      truncatedSixthMassScale N/400 <
        ((Wu2004MeanValue.refinedGood N (947/500)).card : ℝ) ∧
      ∃ p r q : ℕ, p.Prime ∧ (r=1 ∨ r.Prime) ∧ q.Prime ∧
        N=p+r*q ∧ (r:ℝ) ≤ (q:ℝ)^(447/500:ℝ) :=
  refined_1894_from_ordinary_count
    (fun _ he => ordinary_899_with_paid_first hnodes h34 h5 h6 hC3 hC4 he)

end Wu18938Campaign.M3.Confirmed
