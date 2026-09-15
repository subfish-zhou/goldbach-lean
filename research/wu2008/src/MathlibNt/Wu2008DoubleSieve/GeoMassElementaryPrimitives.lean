import MathlibNt.Wu2008DoubleSieve.GeoMassFullReduction

/-! Exact recursive polynomial primitives in the original positive variable. -/
namespace Wu2008DoubleSieve.SecondFunctionalGeometricMass.Elementary
open Set MeasureTheory

noncomputable def momentPolynomial : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, x => x ^ (n + 1) + (n + 1 : ℝ) * momentPolynomial n x

theorem momentPolynomial_zero (n : ℕ) :
    momentPolynomial n 0 = (n.factorial : ℝ) := by
  induction n with
  | zero => simp [momentPolynomial]
  | succ n ih => simp [momentPolynomial, ih, Nat.factorial_succ, Nat.cast_mul]

theorem hasDerivAt_momentPolynomial (n : ℕ) (x : ℝ) :
    HasDerivAt (momentPolynomial n) (momentPolynomial n x - x ^ n) x := by
  induction n with
  | zero => simpa [momentPolynomial] using (hasDerivAt_const x (1 : ℝ))
  | succ n ih =>
    convert! ((hasDerivAt_id x).pow (n + 1)).add (ih.const_mul (n + 1 : ℝ)) using 1
    simp only [momentPolynomial, Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
      mul_one, id_eq]
    ring

noncomputable def momentPrimitive (n : ℕ) (a t : ℝ) : ℝ :=
  -momentPolynomial n (Real.log (t / a)) / t

theorem hasDerivAt_momentPrimitive (n : ℕ) {a t : ℝ} (ha : 0 < a) (ht : 0 < t) :
    HasDerivAt (momentPrimitive n a) (Real.log (t/a)^n / t^2) t := by
  have hlog : HasDerivAt (fun t : ℝ => Real.log (t/a)) (1/t) t := by
    convert! ((hasDerivAt_id t).div_const a).log (ne_of_gt (div_pos ht ha)) using 1
    simp only [id_eq]
    field_simp
  have hP := (hasDerivAt_momentPolynomial n (Real.log (t/a))).comp t hlog
  convert! hP.neg.div (hasDerivAt_id t) ht.ne' using 1
  simp only [id_eq, Function.comp_apply, Pi.neg_apply]
  field_simp
  ring

theorem logPower_intervalIntegrable (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => Real.log (t/a)^n / t^2) volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  simpa only [pow_zero, mul_one] using FullReduction.logMoment_integrable n 0 (b := b) ha

/-- An endpoint expression, defined without any integral. -/
noncomputable def elementaryMomentZero (n : ℕ) (a b : ℝ) : ℝ :=
  (n.factorial : ℝ) / a - momentPolynomial n (Real.log (b/a)) / b

theorem logMoment_zero_eq (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    FullReduction.logMoment n 0 a b = elementaryMomentZero n a b := by
  have hf : (∫ t in a..b, Real.log (t/a)^n / t^2) =
      momentPrimitive n a b - momentPrimitive n a a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hab] at ht
      exact hasDerivAt_momentPrimitive n ha (ha.trans_le ht.1)
    · exact logPower_intervalIntegrable n ha hab
  simp only [FullReduction.logMoment, pow_zero, mul_one]
  rw [hf]
  simp only [momentPrimitive, div_self ha.ne', Real.log_one, momentPolynomial_zero,
    elementaryMomentZero]
  ring

theorem logMoment_one_split (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    FullReduction.logMoment n 1 a b =
      Real.log (b/a) * FullReduction.logMoment n 0 a b -
        FullReduction.logMoment (n+1) 0 a b := by
  have hb := ha.trans_le hab
  have hsplit (t : ℝ) (ht : t ∈ uIcc a b) :
      Real.log (b/t) = Real.log (b/a) - Real.log (t/a) := by
    rw [uIcc_of_le hab] at ht
    have ht0 := ha.trans_le ht.1
    rw [Real.log_div hb.ne' ht0.ne', Real.log_div hb.ne' ha.ne',
      Real.log_div ht0.ne' ha.ne']
    ring
  unfold FullReduction.logMoment
  simp only [pow_zero, pow_one, mul_one]
  calc
    _ = ∫ t in a..b,
        (Real.log (b/a) * (Real.log (t/a)^n / t^2) - Real.log (t/a)^(n+1) / t^2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [hsplit t ht, pow_succ]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub
        ((logPower_intervalIntegrable n ha hab).const_mul _) (logPower_intervalIntegrable (n+1) ha hab),
        intervalIntegral.integral_const_mul]

noncomputable def elementaryMomentOne (n : ℕ) (a b : ℝ) : ℝ :=
  Real.log (b/a) * elementaryMomentZero n a b - elementaryMomentZero (n+1) a b

theorem logMoment_one_eq (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    FullReduction.logMoment n 1 a b = elementaryMomentOne n a b := by
  rw [logMoment_one_split n ha hab, logMoment_zero_eq n ha hab,
    logMoment_zero_eq (n+1) ha hab]
  rfl

noncomputable def momentPrimitiveOne (n : ℕ) (a b t : ℝ) : ℝ :=
  Real.log (b/a) * momentPrimitive n a t - momentPrimitive (n+1) a t

theorem hasDerivAt_momentPrimitiveOne (n : ℕ) {a b t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (ht : 0 < t) :
    HasDerivAt (momentPrimitiveOne n a b)
      (Real.log (t/a)^n * Real.log (b/t) / t^2) t := by
  convert! ((hasDerivAt_momentPrimitive n ha ht).const_mul (Real.log (b/a))).sub
    (hasDerivAt_momentPrimitive (n+1) ha ht) using 1
  rw [Real.log_div hb.ne' ht.ne', Real.log_div hb.ne' ha.ne',
    Real.log_div ht.ne' ha.ne', pow_succ]
  ring

theorem elementaryMomentZero_self (n : ℕ) {a : ℝ} (ha : 0 < a) :
    elementaryMomentZero n a a = 0 := by
  simp [elementaryMomentZero, ha.ne', momentPolynomial_zero]

theorem elementaryMomentOne_self (n : ℕ) {a : ℝ} (ha : 0 < a) :
    elementaryMomentOne n a a = 0 := by
  simp [elementaryMomentOne, elementaryMomentZero_self n ha,
    elementaryMomentZero_self (n+1) ha]

end Wu2008DoubleSieve.SecondFunctionalGeometricMass.Elementary
