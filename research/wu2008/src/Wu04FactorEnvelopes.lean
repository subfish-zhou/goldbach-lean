import Wu04MainConsumer

namespace Wu04FactorEnvelopes
open Wu2008DoubleSieve Real Set MeasureTheory SharpLogRecurrence JointLogTotalComparison
noncomputable section

/-- Exactly one prescribed rational factorization, with no depth parameter. -/
def leftFactor (x : ℝ) : ℝ := (1+x)/2
def rightFactor (x : ℝ) : ℝ := 2*x/(1+x)
def lower (x : ℝ) : ℝ := lowerLog (leftFactor x)+lowerLog (rightFactor x)
def upper (x : ℝ) : ℝ := V (leftFactor x)+V (rightFactor x)

theorem factors {x : ℝ} (hx : 1 ≤ x) :
    1 ≤ leftFactor x ∧ 1 ≤ rightFactor x ∧ leftFactor x*rightFactor x=x := by
  have hp : 0<1+x := by linarith
  refine ⟨by unfold leftFactor; linarith, ?_, ?_⟩
  · unfold rightFactor
    exact (one_le_div hp).2 (by linarith)
  · unfold leftFactor rightFactor
    field_simp

theorem exact_log {x : ℝ} (hx : 1 ≤ x) :
    log x=log (leftFactor x)+log (rightFactor x) := by
  obtain ⟨ha,hb,he⟩ := factors hx
  calc
    log x = log (leftFactor x*rightFactor x) := congrArg log he.symm
    _ = _ := log_mul (by linarith : leftFactor x≠0) (by linarith : rightFactor x≠0)

theorem lower_le_log {x : ℝ} (hx : 1 ≤ x) : lower x ≤ log x := by
  rw [exact_log hx]
  exact add_le_add (log_lower (factors hx).1) (log_lower (factors hx).2.1)

theorem log_le_upper {x : ℝ} (hx : 1 ≤ x) : log x ≤ upper x := by
  rw [exact_log hx]
  exact add_le_add (log_le_V (factors hx).1) (log_le_V (factors hx).2.1)

theorem lower_continuous {x : ℝ} (hx : 0<x) : ContinuousAt lower x := by
  have hl : 0<leftFactor x := by unfold leftFactor; positivity
  have hr : 0<rightFactor x := by unfold rightFactor; positivity
  unfold lower lowerLog
  have hleft : ContinuousAt leftFactor x := by unfold leftFactor; fun_prop
  have hright : ContinuousAt rightFactor x := by
    unfold rightFactor
    fun_prop (disch := positivity)
  fun_prop (disch := positivity)

theorem upper_continuous {x : ℝ} (hx : 0<x) : ContinuousAt upper x := by
  have hl : 0<leftFactor x := by unfold leftFactor; positivity
  have hr : 0<rightFactor x := by unfold rightFactor; positivity
  unfold upper V lowerLog upperLog
  have hleft : ContinuousAt leftFactor x := by unfold leftFactor; fun_prop
  have hright : ContinuousAt rightFactor x := by
    unfold rightFactor
    fun_prop (disch := positivity)
  fun_prop (disch := positivity)

/-- The new lower envelope is applied inside the original anchored J kernel. -/
def jDensity (B A t : ℝ) : ℝ :=
  (log (Wu04MainClassical.a B A)+lower ((A*t-1)/Wu04MainClassical.a B A))/(t*(1-t))
def jIntegral (B A : ℝ) : ℝ := ∫ t in (1-1/B)..(1-1/A), jDensity B A t

theorem j_domain {A B : ℝ} (hB : 2<B) (hBA : B≤A)
    (ha : 1<Wu04MainClassical.a B A) {t : ℝ}
    (ht : t ∈ Icc (1-1/B) (1-1/A)) :
    0<t ∧ t<1 ∧ 1≤(A*t-1)/Wu04MainClassical.a B A := by
  have hB0 : 0<B := by linarith
  have hA0 : 0<A := hB0.trans_le hBA
  have hl : 0<1-1/B := by
    apply sub_pos.mpr
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) (by linarith : (1:ℝ)<B)
  have hu : 1-1/A<1 := sub_lt_self 1 (one_div_pos.mpr hA0)
  refine ⟨hl.trans_le ht.1,ht.2.trans_lt hu,?_⟩
  apply (one_le_div (by linarith : 0<Wu04MainClassical.a B A)).2
  unfold Wu04MainClassical.a
  nlinarith [ht.1]

theorem j_integrable {A B : ℝ} (hB : 2<B) (hBA : B≤A)
    (ha : 1<Wu04MainClassical.a B A) :
    IntervalIntegrable (jDensity B A) volume (1-1/B) (1-1/A) := by
  have hab : 1-1/B≤1-1/A := sub_le_sub_left
    (one_div_le_one_div_of_le (by linarith) hBA) 1
  apply ContinuousOn.intervalIntegrable_of_Icc (μ:=volume) (h:=hab)
  intro t ht
  obtain ⟨ht0,ht1,hx⟩ := j_domain hB hBA ha ht
  apply ContinuousAt.continuousWithinAt
  unfold jDensity
  apply ContinuousAt.div
  · apply continuousAt_const.add
    exact (lower_continuous (by linarith)).comp (by fun_prop)
  · fun_prop
  · exact mul_ne_zero ht0.ne' (by linarith)

theorem j_lower {A B : ℝ} (hB : 2<B) (hBA : B≤A)
    (ha : 1<Wu04MainClassical.a B A) : jIntegral B A ≤ fourthRowClassicalJ B A := by
  have hab : 1-1/B≤1-1/A := sub_le_sub_left
    (one_div_le_one_div_of_le (by linarith) hBA) 1
  apply intervalIntegral.integral_mono_on hab (j_integrable hB hBA ha)
    (fourthRowClassical_J_integrable hBA hB)
  intro t ht
  obtain ⟨ht0,ht1,hx⟩ := j_domain hB hBA ha ht
  have ha0 : 0<Wu04MainClassical.a B A := by linarith
  have hz : 0<A*t-1 := by
    have hh := (one_le_div ha0).1 hx
    linarith
  have hlog := lower_le_log hx
  rw [log_div hz.ne' ha0.ne'] at hlog
  unfold jDensity
  apply div_le_div_of_nonneg_right (by linarith only [hlog])
  exact mul_nonneg ht0.le (by linarith)

/-- No new interval cut: both prescribed factors are integrated on [2,A-1]. -/
def lDensity (t : ℝ) : ℝ := upper (t-1)/t
def lIntegral (A : ℝ) : ℝ := ∫ t in (2:ℝ)..(A-1), lDensity t

theorem l_integrable {A : ℝ} (hA : 3≤A) : IntervalIntegrable lDensity volume 2 (A-1) := by
  apply ContinuousOn.intervalIntegrable_of_Icc (μ:=volume) (h:=by linarith)
  intro t ht
  apply ContinuousAt.continuousWithinAt
  unfold lDensity
  apply ContinuousAt.div
  · exact (upper_continuous (by linarith [ht.1])).comp (by fun_prop)
  · fun_prop
  · linarith [ht.1]

theorem l_upper {A : ℝ} (hA : 3≤A) : fourthRowClassicalL A≤lIntegral A := by
  apply intervalIntegral.integral_mono_on (by linarith)
    (fourthRowClassical_L_integrable (by linarith)) (l_integrable hA)
  intro t ht
  exact div_le_div_of_nonneg_right (log_le_upper (by linarith [ht.1])) (by linarith [ht.1])

end
end Wu04FactorEnvelopes
