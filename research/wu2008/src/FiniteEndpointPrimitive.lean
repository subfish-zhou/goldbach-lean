import FiniteEndpointE

namespace FiniteEndpointPayment
open Wu2008DoubleSieve Real SharpLogRecurrence Set MeasureTheory
open scoped Interval
noncomputable section

/-- Partial fractions of the already permitted cubic Cayley lower function. -/
def pa (q v : ℝ) : ℝ := 8/3-4*v/q+2*v^2/q^2-2*v^3/(3*q^3)
def pb (q v : ℝ) : ℝ := 4*v/q-2*v^2/q^2+2*v^3/(3*q^3)
def pc (q v : ℝ) : ℝ := -2*v^2/q+2*v^3/(3*q^2)
def pd (q v : ℝ) : ℝ := 2*v^3/(3*q)
def primitive (q v t : ℝ) : ℝ :=
  pa q v*log t+pb q v*log (t+q)-pc q v/(t+q)-pd q v/(2*(t+q)^2)
def rationalKernel (q v t : ℝ) : ℝ :=
  (2*(1-v/(t+q))+2/3*(1-v/(t+q))^3)/t

theorem primitive_deriv {q v t : ℝ} (hq : q≠0) (ht : t≠0) (htq : t+q≠0) :
    HasDerivAt (primitive q v) (rationalKernel q v t) t := by
  have dy := (hasDerivAt_id t).add_const q
  have h := ((((hasDerivAt_log ht).const_mul (pa q v)).add
    ((dy.log htq).const_mul (pb q v))).sub
    ((hasDerivAt_const t (pc q v)).div dy htq)).sub
    ((hasDerivAt_const t (pd q v)).div ((dy.pow 2).const_mul 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 htq)))
  convert h using 1 <;> first | rfl | skip
  dsimp [rationalKernel,pa,pb,pc,pd]
  field_simp [hq,ht,htq]
  ring

theorem rational_continuous {q v a b : ℝ} (hab : a≤b)
    (ht : ∀ t∈Icc a b,t≠0) (htq : ∀ t∈Icc a b,t+q≠0) :
    ContinuousOn (rationalKernel q v) (uIcc a b) := by
  rw [uIcc_of_le hab]
  intro t h
  apply ContinuousAt.continuousWithinAt
  unfold rationalKernel
  fun_prop (disch := first | exact ht t h | exact htq t h)

theorem rational_integral {q v a b : ℝ} (hq : q≠0) (hab : a≤b)
    (ht : ∀ t∈Icc a b,t≠0) (htq : ∀ t∈Icc a b,t+q≠0) :
    (∫ t in a..b,rationalKernel q v t)=primitive q v b-primitive q v a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t h
    rw [uIcc_of_le hab] at h
    exact primitive_deriv hq (ht t h) (htq t h)
  · exact (rational_continuous hab ht htq).intervalIntegrable

/-- First odds logarithm after the physical shift t=u+1. -/
theorem first_rational_eq {A u : ℝ} (hA : A≠0) (hu : u+1+A≠0) :
    rationalKernel (1+A) (2*A) u=lowerLog ((u+1)/A)/u := by
  unfold rationalKernel lowerLog
  rw [Wu04FactorJPrimitive.cayley_div hA hu]
  have he : (u+1-A)/(u+1+A)=1-2*A/(u+(1+A)) := by
    rw [show u+(1+A)=u+1+A by ring]
    field_simp [hu]
    ring
  rw [he]
  ring

/-- Reciprocal second odds logarithm; the sign is kept exactly. -/
theorem second_rational_eq {S A u : ℝ} (hd : S-1-u≠0)
    (hu : S-A+(S-1-u)≠0) :
    rationalKernel (-(2*S-A-1)) (-2*(S-A)) u =
      -lowerLog ((S-A)/(S-1-u))/u := by
  unfold rationalKernel lowerLog
  rw [Wu04FactorJPrimitive.cayley_div hd hu]
  have he : (S-A-(S-1-u))/(S-A+(S-1-u))=
      -(1-(-2*(S-A))/(u+(-(2*S-A-1)))) := by
    rw [show u+(-(2*S-A-1))=-(S-A+(S-1-u)) by ring]
    field_simp [hu]
    ring
  rw [he]
  ring

end
end FiniteEndpointPayment
