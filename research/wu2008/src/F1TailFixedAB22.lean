import F1TailPolynomialFTC

noncomputable section
open Real Set MeasureTheory Polynomial
namespace F1TailFixedAB22

/-- Numerator forced by the original reduced denominator's monic normalization. -/
def P : ℝ[X] := C (15132391265909575729959106333/2016456800400000000000000)*X+C (-133693123444211854924371225797/4537027800900000000000000)*X^2+C (909237145996682096458030079779/18148111203600000000000000)*X^3+C (-371819689937947570302424376591/7777761944400000000000000)*X^4+C (342703499435147864830837415951/12444419111040000000000000)*X^5+C (-292296220272828757269466894991/31111047777600000000000000)*X^6+C (65595742289604003898649057797/41481397036800000000000000)*X^7+C (1488502291208034338574092201/96789926419200000000000000)*X^8+C (-645689601104385311825457639409/13937749404364800000000000000)*X^9+C (7004109974740985401908271/2177773344432000000000000)*X^10+C (7558364732982614096927/12444419111040000000000)*X^11+C (-224956971578259167/7777761944400000000)*X^12+C (-233131938895427/41481397036800000)*X^13+C (-14197958309/64814682870000)*X^14+C (-47807573/18148111203600)*X^15+C (844/136110834027)*X^16+C (-25/136110834027)*X^17
/-- Every original pole and its multiplicity is retained. -/
def D : ℝ[X] := (X-C 1)^4*(X-C (2/3))^4*(X-C (-3581/200))^4*(C (4/21)+C (-8/7)*X+C 1*X^2)^1*(C (30769909/40000)+C (10343/100)*X+C 1*X^2)^1

theorem denominator_pos {u : ℝ} (hu : 2 ≤ u) : 0 < D.eval u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u-1 := by linarith
  have ht : 0 < u-2/3 := by linarith
  have hq : 0 < (4:ℝ)/21+(-(8/7))*u+1*u^2 := by
    nlinarith [sq_nonneg (u-2)]
  simp only [D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  simp only [neg_div, sub_neg_eq_add]
  positivity

theorem kernel_exact {u : ℝ} (hu : 2 ≤ u) :
    TailFiniteFTC.AB22.kernel u=P.eval u/D.eval u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u-1 := by linarith
  have ht : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hqm : 0 < (4:ℝ)/21+(-(8/7))*u+1*u^2 := by
    nlinarith [sq_nonneg (u-2)]
  simp only [P, D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  unfold TailFiniteFTC.AB22.kernel F1BFullFTC.quadTwo
  simp only [neg_div, sub_neg_eq_add]
  apply (div_eq_div_iff (by positivity) (by positivity)).2
  ring

theorem numerator_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : 0 ≤ P.eval u := by
  have hk := F1TailPolynomialSigns.AB22_nonneg hu
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

theorem payment_le_mass : payment ≤ TailFiniteFTC.AB22.mass := by
  rw [← TailFiniteFTC.AB22.integral_exact]
  exact F1TailPolynomialFTC.fixed_payment P D TailFiniteFTC.AB22.kernel
    (TailFiniteFTC.AB22.kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num))
    (fun u hu => numerator_nonneg hu) (fun u hu => denominator_pos hu.1)
    (fun u hu => kernel_exact hu.1)

end F1TailFixedAB22
