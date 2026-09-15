import Wu18938Campaign.M3.Confirmed.SecondClassical
import Wu18938Campaign.M3.Confirmed.TerminalSlack

noncomputable section

namespace Wu18938Campaign.M3.Confirmed

open Wu2008DoubleSieve Wu08TerminalAlignment

theorem numericG2_eventual_second_count
    (hnodes : ∀ η : ℝ, 0 < η →
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ρ → δ ≤ 1/100 →
        (6440/10000000:ℝ)-η ≤ wuImprovementLimit false δ (21/5) ∧
        (52233/10000000:ℝ)-η ≤ wuImprovementLimit true δ (16/5))
    {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((9103015/1000000:ℝ)+correctedG2-ε)*truncatedSixthMassScale N ≤
        (sieveCount N 1 N ((N:ℝ)^truncatedSixthLowerBeta) : ℝ) := by
  obtain ⟨T,hT,hc⟩ := correctedG2_eventual_second_count hnodes he
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  have hb : (9103015/1000000:ℝ)+correctedG2-ε ≤ secondMain+correctedG2-ε := by
    linarith only [SecondClassical.second_main_lower]
  exact (mul_le_mul_of_nonneg_right hb
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans (hc N hN hEven)

theorem original_functions_sixth06_slack_C2_paid {δ η G3 G4 G5 G6 : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1/100) (hη : η ≤ 52233/10000000)
    (hh42 : (6440/10000000:ℝ)-η ≤ wuImprovementLimit false δ (21/5))
    (hH32 : (52233/10000000:ℝ)-η ≤ wuImprovementLimit true δ (16/5))
    (hC1 : (14900897/1000000:ℝ) ≤ firstMain)
    (hC3 : thirdMain ≤ (23652925/1000000:ℝ))
    (hC4 : fourthMain ≤ (19643510/1000000:ℝ))
    (hC5 : (1654808/1000000:ℝ) ≤ fifthMain)
    (hC6 : (3819092/1000000:ℝ) ≤ sixthMain)
    (hC7 : seventhMain ≤ (585179/1000000:ℝ))
    (hC8 : eighthMain ≤ (5279581/1000000:ℝ))
    (hC9 : ninthMain ≤ (5372410/1000000:ℝ))
    (hG3 : (39890/1000000:ℝ) ≤ G3)
    (hG4 : (8860/1000000:ℝ) ≤ G4)
    (hG5 : (1359/1000000:ℝ) ≤ G5)
    (hG6 : (3/50:ℝ) ≤ G6) :
    conservativeLedger-(41/20)*η < signedOriginalFunctions δ G3 G4 G5 G6 :=
  original_functions_sixth06_slack hd hh hη hh42 hH32 hC1
    SecondClassical.second_main_lower hC3 hC4 hC5 hC6 hC7 hC8 hC9 hG3 hG4 hG5 hG6

end Wu18938Campaign.M3.Confirmed
