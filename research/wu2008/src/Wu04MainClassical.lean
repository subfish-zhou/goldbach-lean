import Wu04MainProducer

namespace Wu04MainClassical
open Wu2008DoubleSieve Real Set MeasureTheory SharpLogRecurrence JointLogTotalComparison
noncomputable section

def a (B A : ℝ) : ℝ := A*(1-1/B)-1
def b (B A : ℝ) : ℝ := a B A-1
def d (B A : ℝ) : ℝ := A+b B A
def c (B A : ℝ) : ℝ := 8/3-8*a B A/b B A+8*(a B A)^2/(b B A)^2-16*(a B A)^3/(3*(b B A)^3)
def e (B A : ℝ) : ℝ := 8/3-8*a B A/d B A+8*(a B A)^2/(d B A)^2-16*(a B A)^3/(3*(d B A)^3)
def h2 (B A : ℝ) : ℝ := 8*(a B A)^2*(1/d B A-1/b B A)-
  16/3*(a B A)^3*(1/(d B A)^2-1/(b B A)^2)
def h3 (B A : ℝ) : ℝ := -16/3*(a B A)^3*(1/d B A-1/b B A)

def prim (B A t : ℝ) : ℝ := (c B A+log (a B A))*log t -
  (e B A+log (a B A))*log (1-t)+(e B A-c B A)*log (A*t+b B A)-
  h2 B A/(A*t+b B A)-h3 B A/(2*(A*t+b B A)^2)
def density (B A t : ℝ) : ℝ :=
  (log (a B A)+lowerLog ((A*t-1)/a B A))/(t*(1-t))

theorem prim_deriv {A B t : ℝ} (hA : 0 < A) (ha : 1 < a B A)
    (ht : 0 < t) (ht1 : t < 1) : HasDerivAt (prim B A) (density B A t) t := by
  have hb : 0 < b B A := by unfold b; linarith
  have hd : 0 < d B A := by unfold d; positivity
  have hy : A*t+b B A ≠ 0 := by positivity
  have ht' : 1-t ≠ 0 := by linarith
  have hyder := ((hasDerivAt_id t).const_mul A).add_const (b B A)
  have hh := (((((hasDerivAt_log ht.ne').const_mul (c B A+log (a B A))).sub
    ((((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).log ht').const_mul (e B A+log (a B A)))).add
    ((hyder.log hy).const_mul (e B A-c B A))).sub
    ((hasDerivAt_const t (h2 B A)).div hyder hy)).sub
    ((hasDerivAt_const t (h3 B A)).div ((hyder.pow 2).const_mul 2)
      (by simpa using mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) (pow_ne_zero 2 hy)))
  convert hh using 1 <;> first | rfl | skip
  · dsimp [density,lowerLog]
    have ha0 : a B A ≠ 0 := by linarith
    have hb0 := hb.ne'
    have hd0 := hd.ne'
    have hab : A*t-1+a B A = A*t+b B A := by unfold b; ring
    have hq : ((A*t-1)/a B A-1)/((A*t-1)/a B A+1) =
        (A*t-1-a B A)/(A*t+b B A) := by
      have hy' : A*t-1+a B A ≠ 0 := by rw [hab]; exact hy
      field_simp [ha0,hy,hy']
      dsimp [b]
      ring
    rw [hq]
    dsimp [c,e,h2,h3]
    field_simp [ha0,ht.ne',ht',hy,hb0,hd0]
    dsimp [d,b]
    ring

def lowerJ (B A : ℝ) : ℝ := prim B A (1-1/A)-prim B A (1-1/B)

/-- The original lower endpoint anchors the existing universal lowerLog inside the actual J integral. -/
theorem lower_j {A B : ℝ} (hB : 2 < B) (hBA : B ≤ A) (ha : 1 < a B A) :
    lowerJ B A ≤ fourthRowClassicalJ B A := by
  have hA : 0 < A := (show (0:ℝ)<B by linarith).trans_le hBA
  have hab : 1-1/B ≤ 1-1/A := sub_le_sub_left (one_div_le_one_div_of_le (by linarith) hBA) 1
  have hl : 0 < 1-1/B := by
    apply sub_pos.mpr
    simpa only [one_div_one] using one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<1) (by linarith : (1:ℝ)<B)
  have hu : 1-1/A < 1 := sub_lt_self 1 (one_div_pos.mpr hA)
  have ha0 : 0 < a B A := by linarith
  have hp (t : ℝ) (ht : t ∈ Icc (1-1/B) (1-1/A)) :
      0 < t ∧ t < 1 ∧ 1 ≤ (A*t-1)/a B A := by
    refine ⟨hl.trans_le ht.1,ht.2.trans_lt hu,?_⟩
    apply (one_le_div ha0).2
    unfold a
    nlinarith [ht.1]
  have hc : ContinuousOn (density B A) (Icc (1-1/B) (1-1/A)) := by
    unfold density
    apply ContinuousOn.div
    · apply continuousOn_const.add
      unfold lowerLog
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
  have he : (∫ t in (1-1/B)..(1-1/A),density B A t) = lowerJ B A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=prim B A)
    · intro t ht
      rw [uIcc_of_le hab] at ht
      exact prim_deriv hA ha (hp t ht).1 (hp t ht).2.1
    · exact hi
  rw [← he]
  apply intervalIntegral.integral_mono_on hab hi (fourthRowClassical_J_integrable hBA hB)
  intro t ht
  have hz : 0 < A*t-1 := by
    have hh := (one_le_div ha0).1 (hp t ht).2.2
    linarith
  have hlog := log_lower (hp t ht).2.2
  rw [log_div hz.ne' ha0.ne'] at hlog
  unfold density
  exact div_le_div_of_nonneg_right (by linarith only [hlog])
    (mul_nonneg (hp t ht).1.le (by linarith [(hp t ht).2.1]))

/-- Primitive of the old lowerLog in the negative L integrand. -/
def lowerLPrim (t : ℝ) : ℝ := (8/3)*log t+8/t-4/t^2+16/(9*t^3)

theorem lowerLPrim_deriv {t : ℝ} (ht : 0 < t) :
    HasDerivAt lowerLPrim (lowerLog (t-1)/t) t := by
  have hh := ((((hasDerivAt_log ht.ne').const_mul (8/3)).add
    ((hasDerivAt_const t (8:ℝ)).div (hasDerivAt_id t) ht.ne')).sub
    ((hasDerivAt_const t (4:ℝ)).div ((hasDerivAt_id t).pow 2) (pow_ne_zero _ ht.ne'))).add
    ((hasDerivAt_const t (16:ℝ)).div (((hasDerivAt_id t).pow 3).const_mul 9)
      (by simpa using mul_ne_zero (by norm_num : (9:ℝ) ≠ 0) (pow_ne_zero 3 ht.ne')))
  convert hh using 1 <;> first | rfl | (dsimp [lowerLog]; field_simp [ht.ne']; ring)

def vPrim (t : ℝ) : ℝ := (3*upperPrimitive t+2*lowerLPrim t)/5

theorem vPrim_deriv {t : ℝ} (ht : 2 ≤ t) : HasDerivAt vPrim (V (t-1)/t) t := by
  have hh := (((upperPrimitive_derivative ht).const_mul 3).add
    ((lowerLPrim_deriv (by linarith : 0<t)).const_mul 2)).div_const 5
  convert hh using 1 <;> first | rfl | (unfold V; ring)

def upperL (A : ℝ) : ℝ := vPrim (A-1)-vPrim 2

/-- Genuine original-domain L improvement; V is integrated, not only paid at endpoints. -/
theorem upper_l {A : ℝ} (hA : 3 ≤ A) : fourthRowClassicalL A ≤ upperL A := by
  have hab : 2 ≤ A-1 := by linarith
  have hc : ContinuousOn (fun t => V (t-1)/t) (Icc 2 (A-1)) := by
    intro t ht
    have hp : 0<t := by linarith [ht.1]
    have hq : 0<t-1 := by linarith [ht.1]
    apply ContinuousAt.continuousWithinAt
    unfold V lowerLog upperLog
    fun_prop (disch := positivity)
  have hi := hc.intervalIntegrable_of_Icc (μ:=volume) hab
  have he : (∫ t in (2:ℝ)..(A-1), V (t-1)/t) = upperL A := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f:=vPrim)
    · intro t ht
      rw [uIcc_of_le hab] at ht
      exact vPrim_deriv ht.1
    · exact hi
  rw [← he]
  apply intervalIntegral.integral_mono_on hab (fourthRowClassical_L_integrable (by linarith)) hi
  intro t ht
  exact div_le_div_of_nonneg_right (log_le_V (by linarith [ht.1])) (by linarith [ht.1])

#print axioms lower_j
#print axioms upper_l
end
end Wu04MainClassical
