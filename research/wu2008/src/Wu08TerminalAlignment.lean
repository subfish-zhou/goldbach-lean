import Wu08OriginalFirstFormula

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve
namespace Wu08TerminalAlignment
open Wu08OriginalFirstSteps

/-- Exact original fixed first parameter: no substitute cutoff. -/
def firstMain : ℝ := 8*(log (1127/200)+C (1327/200)+E (1327/200))
def secondMain : ℝ := 8*wuLowerCoefficient (1/(2*truncatedSixthLowerBeta))
def thirdMain : ℝ := SingleUpperClassicalLimit.Glin (1/3)
def fourthMain : ℝ := SingleUpperClassicalLimit.Glin truncatedSixthLowerSigma
def fifthMain : ℝ := fifthPairFlin
def sixthMain : ℝ := truncatedSixthLowerF6lin
def seventhMain : ℝ := 8*SeventhEighth.J7
/-- The original 9/(10(1-t)) small-prime weight is already paid in Qtwo. -/
def eighthMain : ℝ := 8*SeventhEighth.J8-8*(U8CanonicalMother.L-U8CanonicalMother.I)
def ninthMain : ℝ := 8*J9
/-- These are the present unweighted upper producers, NOT Wu08's smaller F10/F11. -/
def tenthCurrent : ℝ := 8*FourRoughClosedMass.I10
def eleventhCurrent : ℝ := 8*FourRoughClosedMass.I11

/-- F1 is exactly the complete original twofold-plus-fourfold expression. -/
theorem first_exact : 8*wuLowerCoefficient (1/(2*truncatedSixthLowerAlpha)) = firstMain := by
  have h := lower_terminal (by norm_num : (6:ℝ) ≤ 1327/200) (by norm_num : (1327/200:ℝ) ≤ 8)
  norm_num [truncatedSixthLowerAlpha] at h ⊢
  rw [h]
  rfl

/-- F2's classic main term includes the full, nonzero beyond-four recurrence. -/
theorem second_exact : secondMain = 8*(log (78/25)+C (103/25)) := by
  have h := lower_middle (by norm_num : (4:ℝ) ≤ 103/25) (by norm_num : (103/25:ℝ) ≤ 6)
  norm_num at h
  simpa only [secondMain,truncatedSixthLowerBeta,show (1:ℝ)/(2*(25/206))=103/25 by norm_num] using congrArg (fun x : ℝ => 8*x) h

/-- Actual finite producer, preserving epsilon and threshold, with no numerical premise. -/
theorem first_actual_count {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (firstMain-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (sieveCount N 1 N ((N : ℝ)^truncatedSixthLowerAlpha) : ℝ) := by
  simpa only [first_exact] using BaseLowerCounts.actual_count_lower
    BaseLowerCounts.original_exponents.1 BaseLowerCounts.original_exponents.2.1 hε

/-- Terminal bookkeeping after actual-count payments. Nothing is discarded:
F1 has multiplicity three; the old 47/481250, F2/F5 seeds cancel once. -/
theorem Qtwo_terminal_exact : PositiveTwoPayment.Qtwo =
    (3*firstMain+secondMain-thirdMain-fourthMain+fifthMain+sixthMain-
      2*seventhMain-eighthMain-ninthMain-tenthCurrent-eleventhCurrent+
      8*PositiveSecondPayment.secondGain+PositiveCoreResume.fifthGain+
      FeedbackLimit.Cinf+4*Phase20.rawPsi+4*Phase18.g18)/4 := by
  rw [QtwoWholeLower.Qtwo_identity,JointHMotherPayment.unrounded_coefficient_identity]
  unfold TruncatedElevenClassicalCountLower.classicalCoefficient
  have h1 := first_exact
  unfold secondMain thirdMain fourthMain fifthMain sixthMain seventhMain eighthMain
    ninthMain tenthCurrent eleventhCurrent
  linarith only [h1]

/-- Literal complete first-slot formula, before its factor-three payment. -/
theorem first_original_integrals : firstMain =
    8*(log (1127/200)+
      (∫ t in (3:ℝ)..(1127/200), (∫ u in (2:ℝ)..(t-1), log (u-1)/u)/t)+
      (∫ t in (5:ℝ)..(1127/200), (∫ u in (4:ℝ)..(t-1),
        (∫ v in (3:ℝ)..(u-1), (∫ w in (2:ℝ)..(v-1), log (w-1)/w)/v)/u)/t)) := by
  unfold firstMain
  rw [C_literal (by norm_num : (4:ℝ) ≤ 1327/200),E_literal (by norm_num : (6:ℝ) ≤ 1327/200)]
  norm_num

#print axioms first_actual_count
#print axioms Qtwo_terminal_exact
end Wu08TerminalAlignment
