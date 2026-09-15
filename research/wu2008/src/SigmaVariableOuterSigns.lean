import SigmaVariableCollected

noncomputable section
namespace SigmaVariableOuterPayment
open Real TerminalE SigmaVariableFull

/-- The moving-pole logarithm is eliminated jointly, not assigned a frozen sign. -/
theorem joint_coefficient_balance (p : ℝ) :
    logZeroCoeff p+logNegCoeff p+2*logQuadCoeff p=mainCoeff p := by
  unfold logZeroCoeff logNegCoeff logQuadCoeff mainCoeff zeroOne negOne quadOne
  ring

/-- The first common coefficient is strictly negative on the whole outer interval. -/
theorem zero_coefficient_formula {t : ℝ} (ht : 1 ≤ t) :
    logZeroCoeff (-(t+1))=-(2145*t^2+4418*t+2280)/(210*(t+1)^2) := by
  have ht1 : t+1 ≠ 0 := by linarith
  unfold logZeroCoeff zeroOne TerminalE.h k a b c d TerminalE.e f g
  field_simp
  ring

theorem zero_coefficient_neg {t : ℝ} (ht : 1 ≤ t) :
    logZeroCoeff (-(t+1))<0 := by
  rw [zero_coefficient_formula ht]
  have h : 0<t := by linarith
  apply div_neg_of_neg_of_pos
  · apply neg_neg_of_pos
    positivity
  · positivity

/-- The order-four pole remains in the denominator. -/
theorem neg_coefficient_formula {t : ℝ} (ht : 1 ≤ t) :
    logNegCoeff (-(t+1))=
      64*(10*t^4+18*t^3-t^2-6*t+3)/(945*t^4) := by
  have ht0 : t ≠ 0 := by linarith
  unfold logNegCoeff negOne c d TerminalE.e f
  rw [show -(t+1)+1 = -t by ring]
  field_simp [ht0]
  ring

theorem neg_coefficient_pos {t : ℝ} (ht : 1 ≤ t) :
    0<logNegCoeff (-(t+1)) := by
  rw [neg_coefficient_formula ht]
  have ht0 : 0<t := by linarith
  have hn : 10*t^4+18*t^3-t^2-6*t+3=
      10*(t-1)^4+58*(t-1)^3+113*(t-1)^2+86*(t-1)+24 := by ring
  rw [hn]
  positivity

/-- The quadratic denominator is the original moving-pole denominator. -/
theorem quad_coefficient_formula {t : ℝ} (ht : t ∈ Set.Icc 1 3) :
    logQuadCoeff (-(t+1))=
      250*(-5*t^2+21*t+26)/(189*(-t^2+6*t+6)) := by
  have hq := (SigmaVariableFull.pole_quadratic ht).ne
  unfold q at hq
  have hd : -t^2+6*t+6 ≠ 0 := by
    intro he
    apply hq
    nlinarith only [he]
  unfold logQuadCoeff quadOne TerminalE.residue TerminalE.h k a b c d TerminalE.e f g q
  rw [show (-(t+1))^2+8*-(t+1)+1 = -(-t^2+6*t+6) by ring]
  generalize hs : -t^2+6*t+6 = s at *
  field_simp [hd]
  nlinarith only [hs]

theorem quad_coefficient_pos {t : ℝ} (ht : t ∈ Set.Icc 1 3) :
    0<logQuadCoeff (-(t+1)) := by
  rw [quad_coefficient_formula ht]
  have hp := SigmaVariableFull.pole_quadratic ht
  unfold q at hp
  have hd : 0 < -t^2+6*t+6 := by nlinarith
  have hn : 0 < -5*t^2+21*t+26 := by
    have hm : 0 ≤ t*(3-t) := mul_nonneg (by linarith [ht.1]) (by linarith [ht.2])
    nlinarith [ht.1]
  exact div_pos (mul_pos (by norm_num) hn) (mul_pos (by norm_num) hd)

theorem rad_coefficient_formula {t : ℝ} (ht : t ∈ Set.Icc 1 3) :
    logRadCoeff (-(t+1))=
      250*(-11*t^2+97*t+108)/(189*radical*(-t^2+6*t+6)) := by
  have hq := (SigmaVariableFull.pole_quadratic ht).ne
  have hr := radical_pos.ne'
  unfold q at hq
  have hd : -t^2+6*t+6 ≠ 0 := by
    intro he
    apply hq
    nlinarith only [he]
  unfold logRadCoeff quadZero quadOne TerminalE.residue TerminalE.h k a b c d TerminalE.e f g q
  rw [show (-(t+1))^2+8*-(t+1)+1 = -(-t^2+6*t+6) by ring]
  generalize hs : -t^2+6*t+6 = s at *
  field_simp [hd, hr]
  nlinarith only [hs]

theorem rad_coefficient_pos {t : ℝ} (ht : t ∈ Set.Icc 1 3) :
    0<logRadCoeff (-(t+1)) := by
  rw [rad_coefficient_formula ht]
  have hp := SigmaVariableFull.pole_quadratic ht
  unfold q at hp
  have hd : 0 < -t^2+6*t+6 := by nlinarith
  have hn : 0 < -11*t^2+97*t+108 := by
    have hm : 0 ≤ t*(3-t) := mul_nonneg (by linarith [ht.1]) (by linarith [ht.2])
    nlinarith [ht.1]
  exact div_pos (mul_pos (by norm_num) hn)
    (mul_pos (mul_pos (by norm_num) radical_pos) hd)

end SigmaVariableOuterPayment
