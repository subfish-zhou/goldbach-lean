import Wu04CoupledCostProducer
import MathlibNt.Wu2008DoubleSieve.SharpLogRecurrence

namespace Wu04FullPsiSharp
open Wu2008DoubleSieve Set MeasureTheory Real SharpLogRecurrence
noncomputable section

def c (A : ℝ) : ℝ := 8/3-8/A+8/A^2-16/(3*A^3)
def d (A : ℝ) : ℝ := 8/A-8/A^2+16/(3*A^3)
def e (A : ℝ) : ℝ := -4/A^2+8/(3*A^3)
def f (A : ℝ) : ℝ := 16/(9*A^3)
/-- Partial fractions of the already-proved universal lowerLog, no new order. -/
def primitive (A t : ℝ) : ℝ :=
  c A*(log t-log (1-t)) + d A/t + e A/t^2 + f A/t^3

def lowerJ (B A : ℝ) : ℝ := primitive A (1-1/A)-primitive A (1-1/B)

theorem primitive_deriv {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (primitive A) (lowerLog (A*t-1)/(t*(1-t))) t := by
  have h1 : 1-t ≠ 0 := by linarith
  have h := (((((hasDerivAt_log ht.ne').sub
    (((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).log h1)).const_mul (c A)).add
    ((hasDerivAt_const t (d A)).div (hasDerivAt_id t) ht.ne')).add
    ((hasDerivAt_const t (e A)).div ((hasDerivAt_id t).pow 2) (pow_ne_zero _ ht.ne'))).add
    ((hasDerivAt_const t (f A)).div ((hasDerivAt_id t).pow 3) (pow_ne_zero _ ht.ne'))
  convert h using 1 <;> first | rfl | (dsimp [lowerLog, c, d, e, f]; field_simp; ring)

theorem lower_j {A B : ℝ} (hB : 2 < B) (hBA : B ≤ A)
    (hg : 2 ≤ A*(1-1/B)) : lowerJ B A ≤ fourthRowClassicalJ B A := by
  have hA : 0 < A := (show (0:ℝ) < B by linarith).trans_le hBA
  have hab : 1-1/B ≤ 1-1/A := sub_le_sub_left
    (one_div_le_one_div_of_le (by linarith) hBA) 1
  have ha : 0 < 1-1/B := by
    apply sub_pos.mpr
    simpa only [one_div_one] using one_div_lt_one_div_of_lt
      (by norm_num : (0:ℝ)<1) (by linarith : (1:ℝ)<B)
  have hb : 1-1/A < 1 := sub_lt_self 1 (one_div_pos.mpr hA)
  have hp (t : ℝ) (ht : t ∈ Icc (1-1/B) (1-1/A)) :
      0 < t ∧ t < 1 ∧ 1 ≤ A*t-1 := by
    refine ⟨ha.trans_le ht.1, ht.2.trans_lt hb, ?_⟩
    nlinarith [mul_le_mul_of_nonneg_left ht.1 hA.le]
  have hc : ContinuousOn (fun t => lowerLog (A*t-1)/(t*(1-t)))
      (Icc (1-1/B) (1-1/A)) := by
    apply ContinuousOn.div
    · unfold lowerLog
      apply ContinuousOn.add
      · apply ContinuousOn.const_mul
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro t ht
        linarith [(hp t ht).2.2]
      · apply ContinuousOn.div_const
        apply ContinuousOn.const_mul
        apply ContinuousOn.pow
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro t ht
        linarith [(hp t ht).2.2]
    · fun_prop
    · intro t ht
      exact mul_ne_zero (hp t ht).1.ne' (by linarith [(hp t ht).2.1])
  have hi := hc.intervalIntegrable_of_Icc (μ:=volume) hab
  have he : (∫ t in (1-1/B)..(1-1/A), lowerLog (A*t-1)/(t*(1-t))) = lowerJ B A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=primitive A)
    · intro t ht
      rw [uIcc_of_le hab] at ht
      exact primitive_deriv hA (hp t ht).1 (hp t ht).2.1
    · exact hi
  rw [← he]
  apply intervalIntegral.integral_mono_on hab hi (fourthRowClassical_J_integrable hBA hB)
  intro t ht
  exact div_le_div_of_nonneg_right (log_lower (hp t ht).2.2)
    (mul_nonneg (hp t ht).1.le (by linarith [(hp t ht).2.1]))

/-- Reuses the existing U primitive for both positive-oriented classical L terms. -/
def upperL (A : ℝ) : ℝ := upperPrimitive (A-1)-upperPrimitive 2

theorem upper_l {A : ℝ} (hA : 3 ≤ A) : fourthRowClassicalL A ≤ upperL A := by
  have hab : 2 ≤ A-1 := by linarith
  have hc : ContinuousOn (fun t => upperLog (t-1)/t) (Icc 2 (A-1)) := by
    apply ContinuousOn.div
    · unfold upperLog
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t ht
      have h1 : 0 < t-1 := by linarith [ht.1]
      have ht0 : 0 < t := by linarith [ht.1]
      positivity
    · exact continuousOn_id
    · intro t ht
      linarith [ht.1]
  have hi := hc.intervalIntegrable_of_Icc (μ:=volume) hab
  have he : (∫ t in (2:ℝ)..(A-1), upperLog (t-1)/t) = upperL A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=upperPrimitive)
    · intro t ht
      rw [uIcc_of_le hab] at ht
      exact upperPrimitive_derivative ht.1
    · exact hi
  rw [← he]
  apply intervalIntegral.integral_mono_on hab (fourthRowClassical_L_integrable (by linarith)) hi
  intro t ht
  exact div_le_div_of_nonneg_right (log_upper (by linarith [ht.1])) (by linarith [ht.1])

#print axioms lower_j
#print axioms upper_l
end
end Wu04FullPsiSharp
