import MathlibNt.Wu2008DoubleSieve.HighSixPhase5Envelope

namespace Wu2008DoubleSieve.HighSixPhase5
open Real Set MeasureTheory
noncomputable section

def q : ℝ := 391/325
def r : ℝ := 79/50
def d : ℝ := 179/130
def e : ℝ := 129/50
def baseLog (v : ℝ) : ℝ := log v/(v+1)
def combined (v : ℝ) : ℝ := (2+2*v-179/50)*log v/(2*(179/50-1-v)*(v+1))
def lowerPoly (v : ℝ) : ℝ :=
  (2+2*v-179/50)*(v-1)*(1/d+(v-q)/d^2)*(1/e^2-2*(v-r)/e^3)
def upperPoly (v : ℝ) : ℝ := (v-1)/2-(v-1)^2/(2*q)

theorem log_lower {v : ℝ} (hv : 1 ≤ v) : 2*(v-1)/(v+1) ≤ log v := by
  convert le_log_one_add_of_nonneg (sub_nonneg.mpr hv) using 1 <;> congr 1 <;> ring

theorem log_upper {v : ℝ} (hv : 1 ≤ v) : log v ≤ (v-1/v)/2 := by
  have h := SecondFunctionalFourSevenths.log_chord_bound (a := (1 : ℝ)) (b := v)
    (by norm_num) hv
  norm_num at h
  convert h using 1
  field_simp
  ring

/-- The reciprocal tangent identity is used on a whole positive interval. -/
theorem reciprocal_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1/y+(y-x)/y^2 ≤ 1/x := by
  have hid : 1/x-(1/y+(y-x)/y^2) = (x-y)^2/(x*y^2) := by field_simp; ring
  have hn : 0 ≤ (x-y)^2/(x*y^2) := by positivity
  linarith only [hid,hn]

theorem reciprocal_sq_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    1/y^2-2*(x-y)/y^3 ≤ 1/x^2 := by
  have hid : 1/x^2-(1/y^2-2*(x-y)/y^3) = (x-y)^2*(2*x+y)/(y^3*x^2) := by
    field_simp
    ring
  have hn : 0 ≤ (x-y)^2*(2*x+y)/(y^3*x^2) := by positivity
  linarith only [hid,hn]

theorem combined_lower {v : ℝ} (hv : v ∈ Icc q r) : lowerPoly v ≤ combined v := by
  have hv1 : 1 ≤ v := by norm_num [q] at hv; linarith [hv.1]
  have hD : 0 < 179/50-1-v := by norm_num [r] at hv; linarith [hv.2]
  have hV : 0 < v+1 := by linarith
  have hL : 0 ≤ 2+2*v-(179/50 : ℝ) := by norm_num [q] at hv; linarith [hv.1]
  have ht1 : 1/d+(v-q)/d^2 ≤ 1/(179/50-1-v) := by
    convert reciprocal_tangent hD (show 0 < d by norm_num [d]) using 1; dsimp [d,q]; ring
  have ht2 : 1/e^2-2*(v-r)/e^3 ≤ 1/(v+1)^2 := by
    convert reciprocal_sq_tangent hV (show 0 < e by norm_num [e]) using 1; dsimp [e,r]; ring
  have ht10 : 0 ≤ 1/d+(v-q)/d^2 := by
    have h : 0 ≤ v-q := sub_nonneg.mpr hv.1
    dsimp [d]
    positivity
  have ht20 : 0 ≤ 1/e^2-2*(v-r)/e^3 := by
    have h : v-r ≤ 0 := sub_nonpos.mpr hv.2
    have hd' : 0 < e^3 := by norm_num [e]
    have hn : 2*(v-r)/e^3 ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hd'.le
    have he' : 0 ≤ 1/e^2 := by positivity
    linarith
  calc
    lowerPoly v ≤ (2+2*v-179/50)*(v-1)*(1/(179/50-1-v))*(1/(v+1)^2) := by
      unfold lowerPoly
      gcongr
    _ = (2+2*v-179/50)*(2*(v-1)/(v+1))/(2*(179/50-1-v)*(v+1)) := by field_simp
    _ ≤ combined v := by
      unfold combined
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (log_lower hv1) hL) (by positivity)

theorem baseLog_upper {v : ℝ} (hv : v ∈ Icc 1 q) : baseLog v ≤ upperPoly v := by
  have hv0 : 0 < v := by linarith [hv.1]
  have hvp : 0 < v+1 := by linarith
  have hq : 0 < q := by norm_num [q]
  calc
    baseLog v ≤ ((v-1/v)/2)/(v+1) := div_le_div_of_nonneg_right (log_upper hv.1) hvp.le
    _ = (v-1)/(2*v) := by field_simp; ring
    _ ≤ upperPoly v := by
      have hid : upperPoly v-(v-1)/(2*v) = (v-1)^2*(q-v)/(2*q*v) := by
        unfold upperPoly
        field_simp
        ring
      have hn : 0 ≤ (v-1)^2*(q-v)/(2*q*v) := by
        apply div_nonneg (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hv.2))
        positivity
      linarith only [hid, hn]

end
end Wu2008DoubleSieve.HighSixPhase5
