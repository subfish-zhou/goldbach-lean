import MathlibNt.Wu2008DoubleSieve.JCubicPrimitive

namespace Wu2008DoubleSieve.JCubicActualMass
open Real Set MeasureTheory SharpLogRecurrence SharpJBalance JCubicPrimitive
open scoped Interval

noncomputable def fullDensity (v w t : ℝ) : ℝ :=
  packet (2*v) 0 (2*v) (2*(v-w)) 0 1 1 t+(2/3)*density v w t
noncomputable def fullMass (v w l r : ℝ) : ℝ :=
  (2*v+(2/3)*v^3)*log (crossRatio l r)+
  2*(v-w)*(1/(1-r)-1/(1-l))+
  (2/3)*(rationalPart v w r-rationalPart v w l)

 theorem full_integrable (v w : ℝ) {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (hr : r < 1) :
    IntervalIntegrable (fullDensity v w) volume l r :=
  (packet_integrable hl hlr hr (by norm_num) (by linarith)).add
    ((integrable v w hl hlr hr).const_mul (2/3))

 theorem full_integral (v w : ℝ) {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (hr : r < 1) :
    (∫ t in l..r, fullDensity v w t) = fullMass v w l r := by
  have hi := packet_integrable (A := 2*v) (E := 0) (B := 2*v) (C := 2*(v-w))
    (D := 0) (d := 1) (e := 1) hl hlr hr (by norm_num) (by linarith)
  unfold fullDensity
  rw [intervalIntegral.integral_add hi ((integrable v w hl hlr hr).const_mul (2/3)),
    intervalIntegral.integral_const_mul, integral_mass v w hl hlr hr,
    packet_integral hl hlr hr (by norm_num) (by linarith)]
  have hr0 := hl.trans_le hlr
  have hl1 : 1-l ≠ 0 := by linarith
  have hr1 : 1-r ≠ 0 := by linarith
  dsimp [fullMass,mass,crossRatio]
  rw [log_div hr0.ne' hl.ne',log_div hl1 hr1,
    log_div (mul_ne_zero hr0.ne' hl1) (mul_ne_zero hl.ne' hr1),
    log_mul hr0.ne' hl1,log_mul hl.ne' hr1]
  ring

 theorem fullDensity_eq (v w : ℝ) {t : ℝ} (ht : t ≠ 0) (hu : 1-t ≠ 0) :
    fullDensity v w t =
      (2*((v-w*t)/(1-t))+(2/3)*((v-w*t)/(1-t))^3)/(t*(1-t)) := by
  dsimp [fullDensity,packet,density]
  field_simp [ht,hu]
  ring

 theorem fullDensity_lower (v w q : ℝ) {t : ℝ} (ht : 0 < t) (hu : 0 < 1-t)
    (hq : 1 ≤ q) (he : (q-1)/(q+1) = (v-w*t)/(1-t)) :
    fullDensity v w t ≤ log q/(t*(1-t)) := by
  rw [fullDensity_eq v w ht.ne' hu.ne']
  have h := div_le_div_of_nonneg_right (log_lower hq) (mul_pos ht hu).le
  dsimp only [lowerLog] at h
  rw [he] at h
  have heq : (2 : ℝ)*((v-w*t)/(1-t))+(2/3)*((v-w*t)/(1-t))^3 =
      2*((v-w*t)/(1-t))+2*((v-w*t)/(1-t))^3/3 := by ring
  rw [heq]
  exact h

 theorem seventh_mass_lower : fullMass 1 3 s (1/3) ≤ SeventhEighth.J7 := by
  have hl : 0 < s := by norm_num [s,SeventhEighth.sigma,SeventhEighth.alpha]
  have hlr : s ≤ (1/3 : ℝ) := SeventhEighth.classical_parameters.2.2.le
  have hp (t : ℝ) (ht : t ∈ Icc s (1/3 : ℝ)) :
      fullDensity 1 3 t ≤ log ((1-2*t)/t)/(t*(1-t)) := by
    have ht0 := hl.trans_le ht.1
    have ht1 : 0 < 1-t := by linarith [ht.2]
    apply fullDensity_lower 1 3 ((1-2*t)/t) ht0 ht1
    · exact (le_div_iff₀ ht0).2 (by linarith [ht.2])
    · field_simp [ht0.ne',ht1.ne']
      ring_nf
      field_simp [ht1.ne']
      ring
  have h := intervalIntegral.integral_mono_on hlr
    (full_integrable 1 3 hl hlr (by norm_num)) SeventhEighth.J7_integrable hp
  rw [full_integral 1 3 hl hlr (by norm_num)] at h
  exact h

 theorem eighth_mass_lower : fullMass (1/3) 1 a (1/3) ≤ SeventhEighth.J8 := by
  have hl : 0 < a := SeventhEighth.classical_parameters.1
  have hlr : a ≤ (1/3 : ℝ) := SeventhEighth.classical_parameters.2.1.le.trans
    SeventhEighth.classical_parameters.2.2.le
  have hp (t : ℝ) (ht : t ∈ Icc a (1/3 : ℝ)) :
      fullDensity (1/3) 1 t ≤ log (2-3*t)/(t*(1-t)) := by
    have ht0 := hl.trans_le ht.1
    have ht1 : 0 < 1-t := by linarith [ht.2]
    apply fullDensity_lower (1/3) 1 (2-3*t) ht0 ht1 (by linarith [ht.2])
    have hq : 2-3*t+1 ≠ 0 := by linarith [ht.2]
    field_simp [ht0.ne',ht1.ne',hq]
    ring
  have h := intervalIntegral.integral_mono_on hlr
    (full_integrable (1/3) 1 hl hlr (by norm_num)) SeventhEighth.J8_integrable hp
  rw [full_integral (1/3) 1 hl hlr (by norm_num)] at h
  exact h

 theorem ninth_mass_lower : fullMass (1-2*s) 1 b s ≤ J9 := by
  have hl : 0 < b := by norm_num [b,ninthProfileK2]
  have hlr : b ≤ s := by norm_num [b,s,ninthProfileK2,SeventhEighth.sigma,SeventhEighth.alpha]
  have hr : s < 1/3 := SeventhEighth.classical_parameters.2.2
  have hs0 := hl.trans_le hlr
  have hp (t : ℝ) (ht : t ∈ Icc b s) :
      fullDensity (1-2*s) 1 t ≤ log ((1-s-t)/s)/(t*(1-t)) := by
    have ht0 := hl.trans_le ht.1
    have ht1 : 0 < 1-t := by linarith [ht.2]
    apply fullDensity_lower (1-2*s) 1 ((1-s-t)/s) ht0 ht1
    · exact (le_div_iff₀ hs0).2 (by linarith [ht.2])
    · field_simp [ht0.ne',ht1.ne',hs0.ne']
      ring_nf
      field_simp [ht1.ne']
      ring
  have h := intervalIntegral.integral_mono_on hlr
    (full_integrable (1-2*s) 1 hl hlr (by linarith)) J9_integrable hp
  rw [full_integral (1-2*s) 1 hl hlr (by linarith)] at h
  exact h

end Wu2008DoubleSieve.JCubicActualMass
