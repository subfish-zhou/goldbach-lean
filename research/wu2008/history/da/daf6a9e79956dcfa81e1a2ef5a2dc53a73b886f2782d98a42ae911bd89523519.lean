import RMapMFirstFunctions
import Wu08TerminalAlignment

noncomputable section
open Real Set MeasureTheory
open scoped Interval
open Wu2008DoubleSieve Wu08OriginalFirstSteps

namespace WuPaper.RMapMFirst

abbrev alpha : ℝ := truncatedSixthLowerAlpha
abbrev beta : ℝ := truncatedSixthLowerBeta
abbrev top : ℝ := 1127 / 200
abbrev bottom : ℝ := 1327 / 600

def C1 : ℝ := 8 * wuLowerCoefficient (1 / (2 * alpha))
def C2 : ℝ := 8 * wuLowerCoefficient (1 / (2 * beta))
def denominator (t : ℝ) : ℝ := t * (1 - 2 * alpha * t)
def originalKernel (t : ℝ) : ℝ := wuUpperCoefficient t / denominator t
def C3 : ℝ := 8 * ∫ t in bottom..top, originalKernel t
def C4 : ℝ := 8 * ∫ t in (3 : ℝ)..top, originalKernel t

theorem original_parameters :
    alpha = 100 / 1327 ∧ beta = 25 / 206 ∧
    1 / (2 * alpha) = (1327 / 200 : ℝ) ∧
    1 / (2 * beta) = (103 / 25 : ℝ) ∧
    1 / (6 * alpha) = bottom ∧ 1 / (2 * alpha) - 1 = top := by
  norm_num [alpha, beta, top, bottom, truncatedSixthLowerAlpha, truncatedSixthLowerBeta]

theorem fixed_branch_ranges :
    (6 : ℝ) < 1327 / 200 ∧ (1327 / 200 : ℝ) ≤ 8 ∧
    (4 : ℝ) < 103 / 25 ∧ (103 / 25 : ℝ) ≤ 6 ∧
    0 < bottom ∧ bottom < 3 ∧ (3 : ℝ) < 5 ∧ 5 < top ∧ top < 7 := by
  norm_num [bottom, top]

theorem C1_exact : C1 = Wu08TerminalAlignment.firstMain :=
  Wu08TerminalAlignment.first_exact

theorem C2_exact : C2 = Wu08TerminalAlignment.secondMain := rfl

theorem C1_original :
    C1 = 8 * (log (1127 / 200) +
      (∫ t in (3 : ℝ)..top,
        (∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u) / t) +
      (∫ t in (5 : ℝ)..top,
        (∫ u in (4 : ℝ)..(t - 1),
          (∫ v in (3 : ℝ)..(u - 1),
            (∫ w in (2 : ℝ)..(v - 1), log (w - 1) / w) / v) / u) / t)) := by
  rw [C1_exact, Wu08TerminalAlignment.first_original_integrals]

theorem C2_original :
    C2 = 8 * (log (78 / 25) +
      (∫ t in (3 : ℝ)..(78 / 25),
        (∫ u in (2 : ℝ)..(t - 1), log (u - 1) / u) / t)) := by
  rw [C2_exact, Wu08TerminalAlignment.second_exact, C_literal (by norm_num : (4 : ℝ) ≤ 103/25)]
  norm_num

theorem C3_original :
    C3 = 8 * ∫ t in (1 / (6 * alpha))..(1 / (2 * alpha) - 1),
      wuUpperCoefficient t / (t * (1 - 2 * alpha * t)) := by
  rw [original_parameters.2.2.2.2.1, original_parameters.2.2.2.2.2]
  rfl

theorem C4_original :
    C4 = 8 * ∫ t in (3 : ℝ)..(1 / (2 * alpha) - 1),
      wuUpperCoefficient t / (t * (1 - 2 * alpha * t)) := by
  rw [original_parameters.2.2.2.2.2]
  rfl

theorem denominator_positive {t : ℝ} (ht : t ∈ Icc bottom top) :
    0 < t ∧ 0 < 1 - 2 * alpha * t ∧ 0 < denominator t := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num [bottom]) ht.1
  have hfac : 0 < 1 - 2 * alpha * t := by
    norm_num [alpha, truncatedSixthLowerAlpha, top] at *
    linarith [ht.2]
  exact ⟨ht0, hfac, mul_pos ht0 hfac⟩

theorem kernel_continuous : ContinuousOn originalKernel (Icc bottom top) := by
  apply ContinuousOn.div
  · exact continuousOn_wuUpperCoefficient.mono
      (fun t ht => (denominator_positive ht).1)
  · exact (show Continuous denominator by unfold denominator; fun_prop).continuousOn
  · intro t ht
    exact (denominator_positive ht).2.2.ne'

theorem kernel_integrable {l r : ℝ} (hl : bottom ≤ l) (hlr : l ≤ r) (hr : r ≤ top) :
    IntervalIntegrable originalKernel volume l r := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hlr]
  exact kernel_continuous.mono (fun t ht => ⟨hl.trans ht.1, ht.2.trans hr⟩)

theorem kernel_nonnegative {t : ℝ} (ht : t ∈ Icc bottom top) :
    0 ≤ originalKernel t :=
  div_nonneg (Aa_nonnegative (denominator_positive ht).1).1
    (denominator_positive ht).2.2.le

theorem C34_nonnegative : 0 ≤ C3 ∧ 0 ≤ C4 := by
  constructor
  · apply mul_nonneg (by norm_num)
    exact intervalIntegral.integral_nonneg (by norm_num [bottom, top])
      (fun t ht => kernel_nonnegative ht)
  · apply mul_nonneg (by norm_num)
    exact intervalIntegral.integral_nonneg (by norm_num [top])
      (fun t ht => kernel_nonnegative ⟨by norm_num [bottom] at *; linarith [ht.1], ht.2⟩)

#check @alpha
#print axioms alpha
#check @beta
#print axioms beta
#check @top
#print axioms top
#check @bottom
#print axioms bottom
#check @C1
#print axioms C1
#check @C2
#print axioms C2
#check @denominator
#print axioms denominator
#check @originalKernel
#print axioms originalKernel
#check @C3
#print axioms C3
#check @C4
#print axioms C4
#check @original_parameters
#print axioms original_parameters
#check @fixed_branch_ranges
#print axioms fixed_branch_ranges
#check @C1_exact
#print axioms C1_exact
#check @C2_exact
#print axioms C2_exact
#check @C1_original
#print axioms C1_original
#check @C2_original
#print axioms C2_original
#check @C3_original
#print axioms C3_original
#check @C4_original
#print axioms C4_original
#check @denominator_positive
#print axioms denominator_positive
#check @kernel_continuous
#print axioms kernel_continuous
#check @kernel_integrable
#print axioms kernel_integrable
#check @kernel_nonnegative
#print axioms kernel_nonnegative
#check @C34_nonnegative
#print axioms C34_nonnegative

end WuPaper.RMapMFirst
