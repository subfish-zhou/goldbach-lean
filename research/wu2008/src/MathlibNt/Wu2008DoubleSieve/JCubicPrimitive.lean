import MathlibNt.Wu2008DoubleSieve.CombinedCoefficientEnclosure

namespace Wu2008DoubleSieve.JCubicPrimitive
open Real Set MeasureTheory SharpLogRecurrence SharpJBalance
open scoped Interval

noncomputable def density (v w t : ℝ) : ℝ := (v-w*t)^3/(t*(1-t)^4)
noncomputable def rationalPart (v w t : ℝ) : ℝ :=
  (v^3-w^3)/(1-t)+(v-w)^2*(v+2*w)/(2*(1-t)^2)+(v-w)^3/(3*(1-t)^3)
noncomputable def primitive (v w t : ℝ) : ℝ :=
  v^3*(log t-log (1-t))+rationalPart v w t

 theorem derivative (v w : ℝ) {t : ℝ} (ht : t ≠ 0) (hu : 1-t ≠ 0) :
    HasDerivAt (primitive v w) (density v w t) t := by
  have hd := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
  have h := (((((hasDerivAt_log ht).sub (hd.log hu)).const_mul (v^3)).add
    ((hasDerivAt_const t (v^3-w^3)).div hd hu)).add
    ((hasDerivAt_const t ((v-w)^2*(v+2*w))).div ((hd.pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hu)))).add
    ((hasDerivAt_const t ((v-w)^3)).div ((hd.pow 3).const_mul 3)
      (mul_ne_zero (by norm_num) (pow_ne_zero 3 hu)))
  convert! h using 1
  · ext x; dsimp [primitive,rationalPart]; ring
  · dsimp [density]; field_simp [ht,hu]; ring

 theorem integrable (v w : ℝ) {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (hr : r < 1) :
    IntervalIntegrable (density v w) volume l r := by
  apply ContinuousOn.intervalIntegrable
  unfold density
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro t ht
    rw [uIcc_of_le hlr] at ht
    exact mul_ne_zero (hl.trans_le ht.1).ne' (pow_ne_zero _ (by linarith [ht.2]))

 theorem integral (v w : ℝ) {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (hr : r < 1) :
    (∫ t in l..r, density v w t) = primitive v w r-primitive v w l := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ (integrable v w hl hlr hr)
  intro t ht
  rw [uIcc_of_le hlr] at ht
  exact derivative v w (hl.trans_le ht.1).ne' (by linarith [ht.2])

noncomputable def crossRatio (l r : ℝ) : ℝ := r*(1-l)/(l*(1-r))
noncomputable def mass (v w l r : ℝ) : ℝ :=
  v^3*log (crossRatio l r)+rationalPart v w r-rationalPart v w l

 theorem integral_mass (v w : ℝ) {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (hr : r < 1) :
    (∫ t in l..r, density v w t) = mass v w l r := by
  rw [integral v w hl hlr hr]
  have hr0 := hl.trans_le hlr
  have hl1 : 1-l ≠ 0 := by linarith
  have hr1 : 1-r ≠ 0 := by linarith
  dsimp [primitive,mass,crossRatio]
  rw [log_div (mul_ne_zero hr0.ne' hl1) (mul_ne_zero hl.ne' hr1),
    log_mul hr0.ne' hl1,log_mul hl.ne' hr1]
  ring

 theorem crossRatio_ge_one {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (hr : r < 1) :
    1 ≤ crossRatio l r := by
  apply (le_div_iff₀ (mul_pos hl (sub_pos.mpr hr))).2
  nlinarith

noncomputable def splitLowerLog (q : ℝ) : ℝ := 2*(56/81)+lowerLog (q/4)

 theorem split_log_lower {q : ℝ} (hq : 4 ≤ q) : splitLowerLog q ≤ log q := by
  rw [log_split_four (by linarith : 0 < q)]
  have h := log_lower (t := q/4) (by linarith)
  have h2 := log_two_bounds.1
  dsimp [splitLowerLog]
  linarith

end Wu2008DoubleSieve.JCubicPrimitive
