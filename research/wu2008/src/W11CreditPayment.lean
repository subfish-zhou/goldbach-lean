import W11CreditExpression

noncomputable section
open Real Wu2008DoubleSieve

namespace WuTarget.W11Credit
open SharpLogRecurrence (lowerLog upperLog log_lower)
open JointLogTotalComparison (V log_le_V)

/-- Signs are determined after combining every occurrence in the full credit. -/
def collected (L U : ℝ → ℝ) : ℝ :=
  3058842562664904768103 / 188713714767834375000 -
    76 * U (4 / 3) +
    (531432559600 / 4294306149) * L (3 / 2) +
    (19588418 / 9646875) * L (5 / 4) -
    (12001466293 / 401953125) * U (327 / 200) -
    (50995965659 / 1715000000) * U (527 / 327) -
    (3577926257123 / 107357653725) * U (727 / 527) -
    8 * U (1200 / 727)

theorem packet_collection (f : ℝ → ℝ) : packet f = collected f f := by
  norm_num [packet, alphaPacket, gPacket, endpointPacket, collected,
    ExactWeightTripleEnclosure.tA, ExactWeightTripleEnclosure.tB,
    ExactWeightTripleEnclosure.tC, ExactWeightTripleEnclosure.tD,
    ExactWeightTripleEnclosure.poly, ExactWeightTripleEnclosure.algebraic,
    GConvexChord.m, GConvexChord.C, GConvexChord.r4, GConvexChord.r5,
    VariableGIntegral.logCoefficient, VariableGIntegral.linearCoefficient,
    TotalEndpointComparison.rationalShared, TotalEndpointComparison.A1,
    TotalEndpointComparison.A2, TotalEndpointComparison.A3,
    TotalEndpointComparison.H, TotalEndpointComparison.gap,
    BaseSharedSlack.lowGain, BaseSharedSlack.rate,
    FixedCoefficientUpperEnclosure.a, FixedCoefficientUpperEnclosure.s,
    FixedCoefficientHLowerEnclosure.c, VariableGIntegral.a,
    truncatedSixthLowerAlpha, truncatedSixthLowerSigma]
  ring

theorem credit_collected : WuTarget.W11.correlatedCredit = collected log log := by
  rw [credit_exact, packet_collection]

def payment : ℝ := collected lowerLog V

theorem payment_le_credit : payment ≤ WuTarget.W11.correlatedCredit := by
  have h0 := log_le_V (by norm_num : (1 : ℝ) ≤ 4 / 3)
  have h1 := log_lower (by norm_num : (1 : ℝ) ≤ 3 / 2)
  have h2 := log_lower (by norm_num : (1 : ℝ) ≤ 5 / 4)
  have h3 := log_le_V (by norm_num : (1 : ℝ) ≤ 327 / 200)
  have h4 := log_le_V (by norm_num : (1 : ℝ) ≤ 527 / 327)
  have h5 := log_le_V (by norm_num : (1 : ℝ) ≤ 727 / 527)
  have h6 := log_le_V (by norm_num : (1 : ℝ) ≤ 1200 / 727)
  rw [credit_collected]
  unfold payment collected
  linarith only [h0, h1, h2, h3, h4, h5, h6]

theorem payment_exact :
    payment =
      83001243975163052107842728834523676034673755018536865176775087 /
      61155381611119450770290424186958629545268860216769067968750000 := by
  norm_num [payment, collected, lowerLog, upperLog, V]

theorem payment_bounds :
    (1357218 / 1000000 : ℝ) < payment ∧ payment < 1357219 / 1000000 := by
  rw [payment_exact]
  norm_num

def creditLower : ℝ := 1357218 / 1000000

theorem creditLower_lt_credit : creditLower < WuTarget.W11.correlatedCredit :=
  payment_bounds.1.trans_le payment_le_credit

theorem payment_le_actual :
    payment ≤ 3 * Wu08TerminalAlignment.firstMain -
      Wu08TerminalAlignment.thirdMain - Wu08TerminalAlignment.fourthMain :=
  payment_le_credit.trans WuTarget.W11.actual_correlated_lower

theorem actual_credit_lower :
    (1357218 / 1000000 : ℝ) <
      3 * Wu08TerminalAlignment.firstMain -
        Wu08TerminalAlignment.thirdMain - Wu08TerminalAlignment.fourthMain :=
  creditLower_lt_credit.trans_le WuTarget.W11.actual_correlated_lower

theorem actual_normalized_credit_lower :
    (678609 / 2000000 : ℝ) <
      (3 * Wu08TerminalAlignment.firstMain -
        Wu08TerminalAlignment.thirdMain - Wu08TerminalAlignment.fourthMain) / 4 := by
  linarith only [actual_credit_lower]

end WuTarget.W11Credit
