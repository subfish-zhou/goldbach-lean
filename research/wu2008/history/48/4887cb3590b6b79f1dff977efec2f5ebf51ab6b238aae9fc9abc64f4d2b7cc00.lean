import W14Root

namespace WuTarget.FifthClassicalClosure
open Real Set MeasureTheory Wu2008DoubleSieve SharpMassBalance
noncomputable section

def logCenter : ℝ := 10983/10000
def shapeSlope : ℝ := 1/12-logCenter/16
def shapeCurvature : ℝ := 47/2000
def scalarShape (s : ℝ) : ℝ :=
  logCenter/4+shapeSlope*(s-4)-shapeCurvature*(s-4)^2

def logRemainder (s : ℝ) : ℝ :=
  log (s-1)-log 3-(s-4)/3+(s-4)^2/18-(s-4)^3/(27*(s-1))

theorem log_remainder_derivative {s : ℝ} (hs : 1 < s) :
    HasDerivAt logRemainder ((s-4)^3/(27*(s-1)^2)) s := by
  have h1 := (hasDerivAt_id s).sub_const 1
  have h4 := (hasDerivAt_id s).sub_const 4
  have hn : s-1 ≠ 0 := by linarith
  have hd := ((((h1.log (by simpa only [id_eq] using hn)).sub_const (log 3)).sub
    (h4.div_const 3)).add ((h4.pow 2).div_const 18)).sub
    ((h4.pow 3).div (h1.const_mul 27) (by
      have : s-1 ≠ 0 := by linarith
      simpa only [id_eq] using mul_ne_zero (by norm_num : (27 : ℝ) ≠ 0) this))
  convert hd using 1 <;> first | rfl |
    (simp only [id_eq, Pi.pow_apply]; field_simp [hn]; ring)

theorem log_remainder_nonneg {s : ℝ} (hs : 1 < s) : 0 ≤ logRemainder s := by
  have hzero : logRemainder 4 = 0 := by norm_num [logRemainder]
  by_cases h4 : 4 ≤ s
  · have hc : ContinuousOn logRemainder (Icc 4 s) := by
      intro x hx
      exact (log_remainder_derivative (by linarith [hx.1])).continuousAt.continuousWithinAt
    have hm := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (4 : ℝ) s) hc
      (fun x hx => (log_remainder_derivative (by
        have hh := interior_subset hx
        linarith [hh.1])).hasDerivWithinAt)
      (fun x hx => by
        have hh := interior_subset hx
        exact div_nonneg (pow_nonneg (by linarith [hh.1]) _) (by positivity))
    have hh := hm (show 4 ∈ Icc 4 s from ⟨le_rfl, h4⟩)
      (show s ∈ Icc 4 s from ⟨h4, le_rfl⟩) h4
    rwa [hzero] at hh
  · have h4' : s ≤ 4 := (lt_of_not_ge h4).le
    have hc : ContinuousOn logRemainder (Icc s 4) := by
      intro x hx
      exact (log_remainder_derivative (by linarith [hx.1])).continuousAt.continuousWithinAt
    have hm := antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s (4 : ℝ)) hc
      (fun x hx => (log_remainder_derivative (by
        have hh := interior_subset hx
        linarith [hh.1])).hasDerivWithinAt)
      (fun x hx => by
        have hh := interior_subset hx
        apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
        rw [pow_succ]
        exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (by linarith [hh.2]))
    have hh := hm (show s ∈ Icc s 4 from ⟨le_rfl, h4'⟩)
      (show 4 ∈ Icc s 4 from ⟨h4', le_rfl⟩) h4'
    rwa [hzero] at hh

theorem log_center_lower : logCenter ≤ log (3 : ℝ) := by
  have hl := (FifthLogTotalMagnitude.endpoint_logs (by norm_num : (3 : ℝ) ≤ 4)).1
  have he : logCenter ≤ FifthLogTotalMagnitude.lo 4 := by
    norm_num [logCenter, FifthLogTotalMagnitude.lo, SharpLogRecurrence.lowerLog]
  norm_num only [show (4 : ℝ)-1=3 by norm_num] at hl
  exact he.trans hl

theorem scalar_shape_lower {s : ℝ} (hs : 17/5 ≤ s) :
    scalarShape s ≤ log (s-1)/s := by
  have hs1 : 1 < s := by linarith
  have hrec : -(1/108 : ℝ) ≤ (s-4)/(27*(s-1)) := by
    apply (le_div_iff₀ (by positivity : 0 < 27*(s-1))).2
    linarith
  have hlin : -(3/5 : ℝ)*shapeCurvature ≤ (s-4)*shapeCurvature :=
    mul_le_mul_of_nonneg_right (by linarith) (by norm_num [shapeCurvature])
  have hcoef : 0 ≤ logCenter/16-5/36+4*shapeCurvature+
      (s-4)*shapeCurvature+(s-4)/(27*(s-1)) := by
    norm_num [shapeCurvature, logCenter] at hlin ⊢
    linarith only [hlin, hrec]
  have hmul := mul_nonneg (sq_nonneg (s-4)) hcoef
  have he : logCenter+(s-4)/3-(s-4)^2/18+(s-4)^3/(27*(s-1)) -
      scalarShape s*s =
      (s-4)^2*(logCenter/16-5/36+4*shapeCurvature+
        (s-4)*shapeCurvature+(s-4)/(27*(s-1))) := by
    unfold scalarShape shapeSlope
    ring
  have hr := log_remainder_nonneg hs1
  unfold logRemainder at hr
  apply (le_div_iff₀ (by linarith : 0 < s)).2
  linarith only [hr, log_center_lower, he, hmul]

end
end WuTarget.FifthClassicalClosure
