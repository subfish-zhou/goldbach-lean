import SigmaActualPrimitiveKernelBridge
import SigmaVariableOuterConsumer

noncomputable section
namespace SigmaActualBlockSeparable
open Polynomial Real Set MeasureTheory SigmaHermiteActualFTC SigmaVariableOuterPayment
open NodeExtension FirstFeedbackIntegrals OriginalProfileSigmaPayment ActualNineFeedback
open scoped Interval BigOperators

/-- The derivative is the original paid weight, including both joint endpoints. -/
theorem completePrimitive_deriv_paidWeight {t : ℝ} (ht : t ∈ Icc 1 3) :
    HasDerivAt completePrimitive (paidWeight t) t := by
  rw [paidWeight_completeHermite ht, ← completeKernel_eq_original]
  exact completePrimitive_deriv_kernel ht

/-- Exact endpoint expression, not an integral-defined primitive. -/
def endpointCellMass (a b : ℝ) : ℝ := completePrimitive b - completePrimitive a

theorem paidWeight_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 3) :
    (∫ t in a..b, paidWeight t) = endpointCellMass a b := by
  have hsub : uIcc a b ⊆ Icc (1:ℝ) 3 := by
    rw [uIcc_of_le hab]
    intro t ht
    exact ⟨ha.trans ht.1, ht.2.trans hb⟩
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    exact completePrimitive_deriv_paidWeight (hsub ht)
  · exact (show ContinuousOn paidWeight (uIcc a b) from
      fun t ht => (paidWeight_continuousAt (hsub ht)).continuousWithinAt).intervalIntegrable

theorem nineCell_FTC (k : Fin 9) :
    rationalCellMass (upperLeft k) (upperNode k) =
      endpointCellMass (upperLeft k) (upperNode k) := by
  have hb := cell_bounds (a := 1) le_rfl (by norm_num [upperNode]) k
  have he : cellLeft 1 k = upperLeft k := by
    unfold cellLeft upperLeft
    split_ifs <;> rfl
  rw [he] at hb
  exact paidWeight_integral hb.1 hb.2.1 hb.2.2.1

/-- All nine signed endpoint differences retain the identical original profile weights. -/
def endpointNumerator (z : Fin 9 → ℝ) : ℝ :=
  ∑ k : Fin 9, z k * endpointCellMass (upperLeft k) (upperNode k)

theorem endpointNumerator_eq_rational (z : Fin 9 → ℝ) :
    endpointNumerator z = rationalNumerator z := by
  unfold endpointNumerator rationalNumerator
  apply Finset.sum_congr rfl
  intro k _
  rw [nineCell_FTC]

theorem endpointNumerator_eq_integral (z : Fin 9 → ℝ) :
    endpointNumerator z = ∫ t in (1:ℝ)..3, nineProfile z t * paidWeight t := by
  rw [endpointNumerator_eq_rational, rationalNumerator_integral]

/-- Keep the original maximum branch and unchanged positive denominator. -/
def endpointProfile : ℝ := max CorrectionD0Joint.profile
  (endpointNumerator NineFeedbackStrength.originalH / (1-D0FullDensity.finiteD))

theorem endpointProfile_eq_rational : endpointProfile = rationalProfile := by
  unfold endpointProfile rationalProfile
  rw [endpointNumerator_eq_rational]

theorem endpointProfile_le_actual :
    endpointProfile ≤ aProfile (nineProfile NineFeedbackStrength.originalH) := by
  rw [endpointProfile_eq_rational]
  exact rationalProfile_le_actual

/-- The original signed terminal E contribution is paid exactly once. -/
def endpointTerminal : ℝ := log 2*endpointProfile +
  TerminalESigned.massPaid NineFeedbackStrength.originalH

theorem endpointTerminal_eq_rational : endpointTerminal = rationalTerminal := by
  unfold endpointTerminal rationalTerminal
  rw [endpointProfile_eq_rational]

theorem endpointTerminal_le_actual :
    endpointTerminal ≤ firstFeedback NineFeedbackStrength.originalH 3 3 := by
  rw [endpointTerminal_eq_rational]
  exact rationalTerminal_le_actual

theorem old_terminal_le_endpoint : CorrectionD0Joint.terminal ≤ endpointTerminal := by
  rw [endpointTerminal_eq_rational]
  exact old_terminal_le_rational

end SigmaActualBlockSeparable
