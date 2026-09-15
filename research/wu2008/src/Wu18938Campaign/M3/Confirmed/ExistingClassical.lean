import WE05SixthMajorPayment
import WE07FifthClassicalPayment
import Wu18938Campaign.M3.Confirmed.ConservativeCount
import MathlibNt.Wu2008DoubleSieve.FifthPairEndpoint

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.ExistingClassical

open Real Wu2008DoubleSieve SharpMassBalance WuTarget

theorem sixth_exact_certificate_interval :
    (3810749/1000000:ℝ) ≤ E05SixthMajor.majorLower ∧
      E05SixthMajor.majorLower < 3810750/1000000 := by
  rw [E05SixthMajor.majorLower, E05Sixth.sixthLower_exact]
  norm_num [E05SixthMajor.newCredit, E05SixthMajor.innerCredit,
    E05SixthMajor.innerRate, E05SixthMajor.innerDenom1, E05SixthMajor.innerDenom2,
    E05SixthMajor.fifthExtraCredit, E05SixthMajor.seventhCredit,
    E05SixthMajor.outerCredit, E05Sixth.denominatorCap, E05Sixth.fifthLogTerm,
    E05SixthMajor.z0, Phase25.kx, a, b, lam,
    truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem sixth_main_lower :
    (3810749/1000000:ℝ) ≤ Wu08TerminalAlignment.sixthMain :=
  sixth_exact_certificate_interval.1.trans E05SixthMajor.majorLower_le_actual

theorem fifth_exact_certificate_interval :
    (1651382/1000000:ℝ) ≤ FifthClassicalClosure.rationalLower ∧
      FifthClassicalClosure.rationalLower < 1651383/1000000 := by
  norm_num [FifthClassicalClosure.rationalLower, FifthClassicalClosure.shapeConstant,
    FifthClassicalClosure.endpointLinear, FifthClassicalClosure.shapeLinear,
    FifthClassicalClosure.shapeSquare, FifthClassicalClosure.sumCenter,
    FifthClassicalClosure.shapeSlope, FifthClassicalClosure.shapeCurvature,
    FifthClassicalClosure.logCenter, FifthClassicalClosure.ratioLower,
    SharpLogRecurrence.lowerLog, a, b, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem fifth_main_lower :
    (1651382/1000000:ℝ) ≤ Wu08TerminalAlignment.fifthMain :=
  fifth_exact_certificate_interval.1.trans FifthClassicalClosure.rational_lower

theorem fifth_actual_count {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((1651382/1000000:ℝ)-ε)*truncatedSixthMassScale N ≤ (fifthPairCount N : ℝ) := by
  obtain ⟨T,hT,hc⟩ := fifthPair_actual_lower he
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  have hb := mul_le_mul_of_nonneg_right (sub_le_sub_right fifth_main_lower ε)
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))
  have hcN : (Wu08TerminalAlignment.fifthMain-ε)*truncatedSixthMassScale N ≤
      (fifthPairCount N : ℝ) := by
    simpa only [Wu08TerminalAlignment.fifthMain, truncatedSixthMassScale,
      mul_div_assoc, mul_assoc] using hc N hN hEven
  exact hb.trans hcN

theorem sixth_actual_count {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((3810749/1000000:ℝ)+47/481250-ε)*truncatedSixthMassScale N ≤
        (truncatedSixthMass N ((N:ℝ)^truncatedSixthLowerAlpha)
          ((N:ℝ)^truncatedSixthLowerBeta) ((N:ℝ)^truncatedSixthLowerSigma)
          ((N:ℝ)^truncatedSixthLowerLambda) : ℝ) := by
  obtain ⟨T,hT,hc⟩ := TruncatedSixthSmallDeltaGain.actual_count_lower he
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  have hs : (3810749/1000000:ℝ) ≤ truncatedSixthLowerF6lin := sixth_main_lower
  have hb : (3810749/1000000:ℝ)+47/481250-ε ≤
      truncatedSixthLowerF6lin+47/481250-ε := by
    linarith only [hs]
  have hcN : (truncatedSixthLowerF6lin+47/481250-ε)*truncatedSixthMassScale N ≤
      (truncatedSixthMass N ((N:ℝ)^truncatedSixthLowerAlpha)
        ((N:ℝ)^truncatedSixthLowerBeta) ((N:ℝ)^truncatedSixthLowerSigma)
        ((N:ℝ)^truncatedSixthLowerLambda) : ℝ) := by
    simpa only [truncatedSixthMassScale, mul_div_assoc, mul_assoc] using hc N hN hEven
  exact (mul_le_mul_of_nonneg_right hb
    (truncatedSixthClosure_scale_nonneg (hT.trans hN))).trans hcN

def conservativeClassicalLedger : ℝ :=
  conservativeLedger + ((1651382/1000000 - 1654808/1000000) +
    (3810749/1000000 - 3819092/1000000))/4

theorem conservative_classical_ledger_exact :
    conservativeClassicalLedger = (179227933/200000000:ℝ) := by
  rw [conservativeClassicalLedger, conservativeLedger_exact]
  norm_num

theorem conservative_classical_ledger_unpaid :
    (899/1000:ℝ) - conservativeClassicalLedger = 572067/200000000 ∧
      conservativeClassicalLedger < 899/1000 := by
  rw [conservative_classical_ledger_exact]
  norm_num

end Wu18938Campaign.M3.Confirmed.ExistingClassical
