import JJointPayment

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open SharpLogRecurrence
open HighSharedKernelMagnitude (lowerPrimitive initial_sandwich)
open FixedCoefficientUpperEnclosure (a)
open FixedCoefficientHLowerEnclosure (c)
open Phase22 (u)
namespace MiddleInitialEnvelope

/-- The original initial primitive with an endpoint-ratio logarithmic split. -/
def initialLower (v : ℝ) : ℝ :=
  -20/9+(8/3)*(log (3/2)+lowerLog ((v-1)/3))+8/(v-1)-4/(v-1)^2+16/(9*(v-1)^3)

theorem original_domain_lower {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    initialLower v ≤ wuUpperCoefficient v := by
  have hi := (initial_sandwich (by linarith [hv.1]) hv.2).1
  have hx : 0 < v-1 := by linarith [hv.1]
  have hl := log_lower (show 1 ≤ (v-1)/3 by linarith [hv.1])
  have he : log (v-1)-log 2 = log (3/2:ℝ)+log ((v-1)/3) := by
    rw [log_div (by norm_num : (3:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0),
      log_div hx.ne' (by norm_num : (3:ℝ) ≠ 0)]
    ring
  norm_num [lowerPrimitive] at hi
  unfold initialLower
  linarith only [hi,hl,he]

/-- Fixed original lowerLog endpoint payment, with no new log approximation. -/
def rationalLower (v : ℝ) : ℝ :=
  44/9+(8/3)*lowerLog (3/2)+8/(v-1)-4/(v-1)^2+16/(9*(v-1)^3)-
    64/(v+2)+192/(v+2)^2-384/(v+2)^3

theorem rational_form {v : ℝ} (hv : 4 ≤ v) :
    initialLower v = rationalLower v+(8/3)*(log (3/2)-lowerLog (3/2)) := by
  have hx : v-1 ≠ 0 := by linarith
  have hy : v+2 ≠ 0 := by linarith
  have he : ((v-1)/3-1)/((v-1)/3+1)=(v-4)/(v+2) := by
    apply (div_eq_div_iff (show (v-1)/3+1 ≠ 0 by linarith) hy).2
    ring
  unfold initialLower rationalLower
  simp only [lowerLog,he]
  field_simp [hx,hy]
  ring

theorem rational_lower {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    rationalLower v ≤ wuUpperCoefficient v := by
  have h := original_domain_lower hv
  rw [rational_form hv.1] at h
  have hl := log_lower (by norm_num : (1:ℝ) ≤ 3/2)
  linarith only [h,hl]

/-- The exact quadratic lower function paid by the original middle upper. -/
def oldLower (v : ℝ) : ℝ :=
  (5-v)*(34832/30375)+(v-4)*(541588/385875)-(v-4)*(5-v)/22

def gainDensity (v : ℝ) : ℝ := rationalLower v-oldLower v

theorem middle_pointwise {v : ℝ} (hv : v ∈ Icc (4:ℝ) 5) :
    GConvexChord.C+GConvexChord.m*v-wuUpperCoefficient v ≤
      JointSharedTightEnclosure.middleHi v-gainDensity v := by
  have h := rational_lower hv
  unfold JointSharedTightEnclosure.middleHi gainDensity oldLower GConvexChord.C GConvexChord.m
  linarith only [h]

end MiddleInitialEnvelope
