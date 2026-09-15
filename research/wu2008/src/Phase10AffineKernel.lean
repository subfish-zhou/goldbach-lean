import MathlibNt.Wu2008DoubleSieve.HighSixPhase9Feedback

namespace Wu2008DoubleSieve.Phase10
open Real Set MeasureTheory
noncomputable section

/-- The literal rational kernel is continuous away from its two poles. -/
theorem weighted_affine_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) (A B : ℝ) :
    IntervalIntegrable (fun u : ℝ => (A-B*u)/(u*(1-u))) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro u hu
  exact ne_of_gt (mul_pos (lt_of_lt_of_le ha hu.1) (by linarith [hu.2]))

/-- True FTC for the affine numerator, with the logarithmic domains discharged. -/
theorem weighted_affine_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < 1) (A B : ℝ) :
    (∫ u in a..b, (A-B*u)/(u*(1-u))) =
      A*log (b/a)+(A-B)*log ((1-a)/(1-b)) := by
  have hd : ∀ u ∈ uIcc a b, HasDerivAt
      (fun x : ℝ => A*log x-(A-B)*log (1-x)) ((A-B*u)/(u*(1-u))) u := by
    intro u hu
    rw [uIcc_of_le hab] at hu
    have hu0 : u ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hu.1)
    have hu1 : 1-u ≠ 0 := ne_of_gt (by linarith [hu.2])
    have hh := ((hasDerivAt_log hu0).const_mul A).sub
      ((((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).log hu1).const_mul (A-B))
    dsimp only [Pi.sub_apply, id_eq] at hh
    convert hh using 1 <;> first | rfl | (field_simp; ring)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (weighted_affine_integrable ha hab hb A B)
  rw [log_div (ne_of_gt (ha.trans_le hab)) (ne_of_gt ha),
    log_div (ne_of_gt (by linarith : 0 < 1-a)) (ne_of_gt (by linarith : 0 < 1-b))]
  rw [hf]
  ring

/-- Exact coefficient from the unchanged endpoints and unchanged affine shape. -/
def L : ℝ := (18/13)*log (1677/1432)+(1/130)*log (179/130)

theorem literal_affine_integral (A : ℝ) :
    (∫ u in (8/13 : ℝ)..(129/179), (A*(5/13)*(18/5-(179/50)*u))/(u*(1-u))) = A*L := by
  have he : (fun u : ℝ => (A*(5/13)*(18/5-(179/50)*u))/(u*(1-u))) =
      (fun u : ℝ => (A*(18/13)-(A*(179/130))*u)/(u*(1-u))) := by
    funext u
    congr 1
    ring
  rw [he, weighted_affine_integral (by norm_num) (by norm_num) (by norm_num)]
  norm_num
  unfold L
  ring

/-- The actual weighted lower function consumes the full affine envelope. -/
theorem weighted_h_log_lower {δ : ℝ} (hδ : 0 < δ) (hδhi : δ ≤ 1/100) :
    HighSixPhase9.amplitude δ*L ≤
      ∫ u in (8/13 : ℝ)..(129/179), wuImprovementLimit false δ ((179/50)*u)/(u*(1-u)) := by
  rw [← literal_affine_integral]
  have hi : IntervalIntegrable
      (fun u : ℝ => (HighSixPhase9.amplitude δ*(5/13)*(18/5-(179/50)*u))/(u*(1-u)))
      volume (8/13) (129/179) := by
    have he : (fun u : ℝ => (HighSixPhase9.amplitude δ*(5/13)*(18/5-(179/50)*u))/(u*(1-u))) =
        (fun u : ℝ => (HighSixPhase9.amplitude δ*(18/13)-
          (HighSixPhase9.amplitude δ*(179/130))*u)/(u*(1-u))) := by
      funext u
      congr 1
      ring
    rw [he]
    exact weighted_affine_integrable (by norm_num) (by norm_num) (by norm_num) _ _
  apply intervalIntegral.integral_mono_on (by norm_num) hi
    (HighSixPhase9.weighted_h_integrable hδ hδhi)
  intro u hu
  apply div_le_div_of_nonneg_right _ (le_of_lt (mul_pos (by linarith [hu.1])
    (by linarith [hu.2])))
  exact HighSixPhase9.h_linear hδ hδhi ⟨by linarith [hu.1],by linarith [hu.2]⟩

end
end Wu2008DoubleSieve.Phase10
