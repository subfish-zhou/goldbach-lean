import F1TailPolynomialFTC

noncomputable section
open Real Set MeasureTheory Polynomial
namespace F1TailFixedBA12

/-- Numerator forced by the original reduced denominator's monic normalization. -/
def P : ℝ[X] := C (-106693315103171395599636806361/1129259373648700000000000000)+C (1705597323543979387888793990571/3952407807770450000000000000)*X+C (-54942995007847400246718640355601/15809631231081800000000000000)*X^2+C (-7434166832370711030668482268163/3161926246216360000000000000)*X^3+C (3320656359138806520648744819603/1580963123108180000000000000)*X^4+C (20003213701321570181394904257/8016038144800000000000000)*X^5+C (-53383989539540647664424331241121/36136299956758400000000000000)*X^6+C (-15630118253557888468281569984611/36136299956758400000000000000)*X^7+C (10446409657273586519280957054167/29140312285129973760000000000)*X^8+C (793501836891696141016444079/607089839273541120000000000)*X^9+C (-14543443614446873775670209/404726559515694080000000)*X^10+C (55730364579828986148383/11382934486378896000000)*X^11+C (13934344783785753323/10840889987027520000)*X^12+C (-3691370799445657/11615239271815200)*X^13+C (-7540031526623/813066749027064)*X^14+C (5179598141500/711433405398681)*X^15+C (-9586547500/30931887191247)*X^16+C (-40435000000/711433405398681)*X^17+C (3100000000/711433405398681)*X^18
/-- Every original pole and its multiplicity is retained. -/
def D : ℝ[X] := (X-C 0)^3*(X-C (-2))^4*(X-C (-3581/200))^4*(C 4+C 16*X+C 1*X^2)^1*(C (30769909/40000)+C (10343/100)*X+C 1*X^2)^1

theorem denominator_pos {u : ℝ} (hu : 2 ≤ u) : 0 < D.eval u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u-1 := by linarith
  have ht : 0 < u-2/3 := by linarith
  have hq : 0 < (4:ℝ)/21+(-8/7)*u+u^2 := by
    nlinarith [sq_nonneg (u-2)]
  simp only [D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  positivity

theorem kernel_exact {u : ℝ} (hu : 2 ≤ u) :
    TailFiniteFTC.BA12.kernel u=P.eval u/D.eval u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u-1 := by linarith
  have ht : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hqm : 0 < (4:ℝ)/21+(-8/7)*u+u^2 := by
    nlinarith [sq_nonneg (u-2)]
  simp only [P, D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  unfold TailFiniteFTC.BA12.kernel F1BFullFTC.quadTwo
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  ring

theorem numerator_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : 0 ≤ P.eval u := by
  have hk := F1TailPolynomialSigns.BA12_nonneg hu
  rw [kernel_exact hu.1] at hk
  simpa only [zero_mul] using (le_div_iff₀ (denominator_pos hu.1)).mp hk

def W : ℝ := F1TailPolynomialFTC.moment P
def J : ℝ := F1TailPolynomialFTC.moment (P*D)
def a : ℝ := W/J
def payment : ℝ := W^2/J

theorem W_exact : (∫ u in (2:ℝ)..(927/200), P.eval u)=W :=
  F1TailPolynomialFTC.moment_exact P

theorem J_exact : (∫ u in (2:ℝ)..(927/200), P.eval u*D.eval u)=J := by
  simpa only [Polynomial.eval_mul, J] using F1TailPolynomialFTC.moment_exact (P*D)

theorem payment_le_mass : payment ≤ TailFiniteFTC.BA12.mass := by
  rw [← TailFiniteFTC.BA12.integral_exact]
  exact F1TailPolynomialFTC.fixed_payment P D TailFiniteFTC.BA12.kernel
    (TailFiniteFTC.BA12.kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num))
    (fun u hu => numerator_nonneg hu) (fun u hu => denominator_pos hu.1)
    (fun u hu => kernel_exact hu.1)

end F1TailFixedBA12
