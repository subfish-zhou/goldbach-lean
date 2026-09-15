import Wu08TerminalAlignment

/-! Original small-prime weights for F10/F11. Exact missing DEBITS, not paid gains. -/
noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve FourRoughClosedMass
namespace Wu08OriginalFourWeights

def original (O : ℝ → ℝ) : ℝ :=
  (36/5)*(∫ x in alpha..(1/10:ℝ), O x/(1-x))+
    8*(∫ x in (1/10:ℝ)..beta, O x)
def missing (O : ℝ → ℝ) : ℝ :=
  8*(∫ x in alpha..(1/10:ℝ), ((1/10-x)/(1-x))*O x)

def original10 : ℝ := original regularOuter10
def original11 : ℝ := original regularOuter11
def debit10 : ℝ := missing regularOuter10
def debit11 : ℝ := missing regularOuter11

theorem parameters : alpha ≤ (1/10:ℝ) ∧ (1/10:ℝ) ≤ beta ∧ beta < 1 := by
  norm_num [alpha,beta,truncatedSixthLowerAlpha,truncatedSixthLowerBeta]

theorem weighted_integrable {O : ℝ → ℝ} (hO : Continuous O) :
    IntervalIntegrable (fun x => O x/(1-x)) volume alpha (1/10:ℝ) := by
  apply ContinuousOn.intervalIntegrable
  apply hO.continuousOn.div (by fun_prop)
  intro x hx
  rw [uIcc_of_le parameters.1] at hx
  linarith [hx.2]

theorem missing_integrable {O : ℝ → ℝ} (hO : Continuous O) :
    IntervalIntegrable (fun x => ((1/10-x)/(1-x))*O x) volume alpha (1/10:ℝ) := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.mul _ hO.continuousOn
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro x hx
  rw [uIcc_of_le parameters.1] at hx
  linarith [hx.2]

/-- Unit outer weight minus the original weight is the full positive small-window debit. -/
theorem exact_debit {O : ℝ → ℝ} (hO : Continuous O) :
    8*(∫ x in alpha..beta, O x) = original O+missing O := by
  have hi := hO.intervalIntegrable (μ := volume) alpha (1/10:ℝ)
  have hj := hO.intervalIntegrable (μ := volume) (1/10:ℝ) beta
  have hw := weighted_integrable hO
  have hd := missing_integrable hO
  have hp : (36/5)*(∫ x in alpha..(1/10:ℝ), O x/(1-x))+
      8*(∫ x in alpha..(1/10:ℝ), ((1/10-x)/(1-x))*O x) =
      8*(∫ x in alpha..(1/10:ℝ), O x) := by
    rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hw.const_mul (36/5)) (hd.const_mul 8),
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp only
    rw [uIcc_of_le parameters.1] at hx
    have hn : 1-x ≠ 0 := by linarith [hx.2]
    field_simp [hn]
    ring
  have ha := intervalIntegral.integral_add_adjacent_intervals hi hj
  unfold original missing
  linarith only [hp,ha]

theorem missing_nonneg {O : ℝ → ℝ}
    (hO : ∀ x ∈ Icc alpha (1/10:ℝ), 0 ≤ O x) : 0 ≤ missing O := by
  unfold missing
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg parameters.1
  intro x hx
  exact mul_nonneg (div_nonneg (by linarith [hx.2]) (by linarith [hx.2])) (hO x hx)

theorem outer10_nonneg {x : ℝ} (hx : x ∈ Icc alpha beta) : 0 ≤ regularOuter10 x := by
  apply intervalIntegral.integral_nonneg hx.2
  intro y hy
  apply intervalIntegral.integral_nonneg hy.2
  intro z hz
  exact intervalIntegral.integral_nonneg_of_forall hz.2 (regularKernel_nonneg x y z)

theorem outer11_nonneg {x : ℝ} (hx : x ∈ Icc alpha beta) : 0 ≤ regularOuter11 x := by
  apply intervalIntegral.integral_nonneg hx.2
  intro y hy
  apply intervalIntegral.integral_nonneg hy.2
  intro z hz
  apply intervalIntegral.integral_nonneg_of_forall
    (by linarith [hz.2,fixed_geometry.2.2.2.2.2.2.1])
  exact regularKernel_nonneg x y z

theorem actual_tenth_debit : Wu08TerminalAlignment.tenthCurrent = original10+debit10 := by
  unfold Wu08TerminalAlignment.tenthCurrent original10 debit10
  rw [I10_eq_regular]
  exact exact_debit regularOuter10_continuous

theorem actual_eleventh_debit : Wu08TerminalAlignment.eleventhCurrent = original11+debit11 := by
  unfold Wu08TerminalAlignment.eleventhCurrent original11 debit11
  rw [I11_eq_regular]
  exact exact_debit regularOuter11_continuous

theorem debits_nonnegative : 0 ≤ debit10 ∧ 0 ≤ debit11 := by
  constructor
  · exact missing_nonneg (fun _ hx => outer10_nonneg ⟨hx.1,hx.2.trans parameters.2.1⟩)
  · exact missing_nonneg (fun _ hx => outer11_nonneg ⟨hx.1,hx.2.trans parameters.2.1⟩)

/-- The present coefficient cannot be renamed as the original weighted terminal:
its missing finite-producer improvements must be explicitly DEBITED. -/
theorem Qtwo_original_weight_debits : PositiveTwoPayment.Qtwo =
    (3*Wu08TerminalAlignment.firstMain+Wu08TerminalAlignment.secondMain-
      Wu08TerminalAlignment.thirdMain-Wu08TerminalAlignment.fourthMain+
      Wu08TerminalAlignment.fifthMain+Wu08TerminalAlignment.sixthMain-
      2*Wu08TerminalAlignment.seventhMain-Wu08TerminalAlignment.eighthMain-
      Wu08TerminalAlignment.ninthMain-original10-original11+
      8*PositiveSecondPayment.secondGain+PositiveCoreResume.fifthGain+
      FeedbackLimit.Cinf+4*Phase20.rawPsi+4*Phase18.g18-debit10-debit11)/4 := by
  rw [Wu08TerminalAlignment.Qtwo_terminal_exact,actual_tenth_debit,actual_eleventh_debit]
  ring

#print axioms actual_tenth_debit
#print axioms actual_eleventh_debit
#print axioms debits_nonnegative
#print axioms Qtwo_original_weight_debits
end Wu08OriginalFourWeights
