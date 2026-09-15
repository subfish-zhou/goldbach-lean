import CrossFactors

noncomputable section
open Real Set FirstIntegralRecovery FirstCRationalPayment F1BFullFTC FreshRemainingFactors
open Wu2008DoubleSieve SharpLogRecurrence F1SecondLogRecovery
namespace F1FactorCross

def kA1 (u : ℝ) : ℝ := (u-2)^5*(210*u^2*(u+2)+(u-2)^2*(5*u+14))/
  (210*u^2*(u+2)^4*(u^2+16*u+4))
def kA2 (u : ℝ) : ℝ := (u-2)^5*(840*(u-1)^2*(3*u-2)+(u-2)^2*(17*u-10))/
  (840*(u-1)^2*(3*u-2)^4*(21*u^2-24*u+4))
def kB1 (u : ℝ) : ℝ := (927/200-u)^5*
  (210*(u+1327/200)^2*(3*u+1727/200)+(927/200-u)^2*(19*u+9435/200))/
  (210*(u+1327/200)^2*(3*u+1727/200)^4*F1BFullFTC.quadOne u)
def kB2 (u : ℝ) : ℝ := (927/200-u)^5*
  (840*(1127/200)^2*(u+3581/200)+(927/200-u)^2*(7*u+20559/200))/
  (840*(1127/200)^2*(u+3581/200)^4*F1BFullFTC.quadTwo u)
def aDiff (u : ℝ) : ℝ := 2*(u-2)^3/(3*(u+2)^3)+2*(u-2)^3/(3*(3*u-2)^3)
def bDiff (u : ℝ) : ℝ :=
  2*(927/200-u)/(3*u+1727/200)+2*(927/200-u)^3/(3*(3*u+1727/200)^3)+
  (2*(927/200-u)/(u+3581/200)+2*(927/200-u)^3/(3*(u+3581/200)^3))-
  2*(927/200-u)/(u+1327/200)

theorem keptA_exact {u : ℝ} (hu : 2 ≤ u) : kept (u-1)=kA1 u+kA2 u := by
  have hx : 1 ≤ u-1 := by linarith
  have hp : 0 < u-1 := by linarith
  have hu0 : 0 < u := by linarith
  have ht : 0 < 3*u-2 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  unfold kept splitFresh
  rw [gap_rational hx,F1FreshFTC.residual_first hp,F1FreshFTC.residual_second hp]
  unfold kA1 kA2
  have hv : 0 ≤ u-2 := by linarith
  generalize he : u-2=v at hv
  have heq : u=v+2 := by linarith
  rw [heq]
  ring_nf
  field_simp
  ring

theorem keptB_exact {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : kept (ratio u)=kB1 u+kB2 u := by
  have hu0 : 0 < u := by linarith [hu.1]
  have hv : 0 < u+1 := by linarith [hu.1]
  have hk : 0 < (1127:ℝ)/200 := by norm_num
  have hr : 1 ≤ ratio u := ratio_ge_one
    (show u ∈ Icc 2 ((1327:ℝ)/200-2) by constructor <;> linarith [hu.1,hu.2])
  unfold kept splitFresh
  rw [gap_rational hr]
  unfold ratio
  norm_num only [show (1327:ℝ)/200-1=1127/200 by norm_num]
  rw [scaled_error_one hk hv,scaled_error_two hk hv,
    F1FreshFTC.scaled_first hk hv,F1FreshFTC.scaled_second hk hv]
  unfold kB1 kB2 F1BFullFTC.quadOne F1BFullFTC.quadTwo
  ring_nf
  field_simp
  ring

theorem aDiff_exact {u : ℝ} (hu : 2 ≤ u) : factorA u=aDiff u := by
  have hu0 : 0 < u := by linarith
  have hum : 0 < u-1 := by linarith
  have ht : 0 < 3*u-2 := by linarith
  unfold factorA splitL lowerLog linearA aDiff
  have hv : 0 ≤ u-2 := by linarith
  generalize he : u-2=v at hv
  have heq : u=v+2 := by linarith
  rw [heq]
  ring_nf
  field_simp (disch := positivity)
  ring

theorem bDiff_exact {u : ℝ} (hu : 2 ≤ u) : splitL (ratio u)-linearB u=bDiff u := by
  have hu0 : 0 < u := by linarith
  unfold splitL ratio lowerLog linearB bDiff
  field_simp
  ring

theorem cross_rational {u : ℝ} (hu : u ∈ Icc 2 (927/200)) :
    cross u = (kA1 u*bDiff u+kA2 u*bDiff u+kA1 u*kB1 u+kA1 u*kB2 u+
      kA2 u*kB1 u+kA2 u*kB2 u+aDiff u*kB1 u+aDiff u*kB2 u)/u := by
  unfold cross crossA crossB rationalB
  rw [keptA_exact hu.1,keptB_exact hu,aDiff_exact hu.1]
  have h := bDiff_exact hu.1
  linear_combination (kA1 u+kA2 u)/u*h

end F1FactorCross
