import F1TailPolynomialFTC

noncomputable section
open Real Set MeasureTheory Polynomial
namespace F1TailFixedAB12

/-- Numerator forced by the original reduced denominator's monic normalization. -/
def P : ℝ[X] := C (45397173797728727189877318999/55568143750000000000)+C (-133693123444211854924371225797/41676107812500000000)*X+C (909237145996682096458030079779/166704431250000000000)*X^2+C (-371819689937947570302424376591/71444756250000000000)*X^3+C (342703499435147864830837415951/114311610000000000000)*X^4+C (-292296220272828757269466894991/285779025000000000000)*X^5+C (65595742289604003898649057797/381038700000000000000)*X^6+C (1488502291208034338574092201/889090300000000000000)*X^7+C (-645689601104385311825457639409/128029003200000000000000)*X^8+C (7004109974740985401908271/20004531750000000000)*X^9+C (7558364732982614096927/114311610000000000)*X^10+C (-224956971578259167/71444756250000)*X^11+C (-233131938895427/381038700000)*X^12+C (-56791833236/2381491875)*X^13+C (-191230292/666817725)*X^14+C (54016/80018127)*X^15+C (-1600/80018127)*X^16
/-- Every original pole and its multiplicity is retained. -/
def D : ℝ[X] := (X-C 0)^5*(X-C (-2))^4*(X-C (-3581/200))^4*(C 4+C 16*X+C 1*X^2)^1*(C (30769909/40000)+C (10343/100)*X+C 1*X^2)^1

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
    TailFiniteFTC.AB12.kernel u=P.eval u/D.eval u := by
  have hu0 : 0 < u := by linarith
  have hu1 : 0 < u-1 := by linarith
  have ht : 0 < u-2/3 := by linarith
  have hq : 0 < 21*u^2-24*u+4 := by nlinarith [sq_nonneg (u-2)]
  have hqm : 0 < (4:ℝ)/21+(-8/7)*u+u^2 := by
    nlinarith [sq_nonneg (u-2)]
  simp only [P, D, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub,
    Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
  unfold TailFiniteFTC.AB12.kernel F1BFullFTC.quadTwo
  simp only [neg_div, sub_neg_eq_add, sub_zero]
  field_simp (disch := positivity)
  ring

theorem numerator_nonneg {u : ℝ} (hu : u ∈ Icc 2 (927/200)) : 0 ≤ P.eval u := by
  have hk := F1TailPolynomialSigns.AB12_nonneg hu
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

theorem payment_le_mass : payment ≤ TailFiniteFTC.AB12.mass := by
  rw [← TailFiniteFTC.AB12.integral_exact]
  exact F1TailPolynomialFTC.fixed_payment P D TailFiniteFTC.AB12.kernel
    (TailFiniteFTC.AB12.kernel_continuousOn.intervalIntegrable_of_Icc (by norm_num))
    (fun u hu => numerator_nonneg hu) (fun u hu => denominator_pos hu.1)
    (fun u hu => kernel_exact hu.1)

end F1TailFixedAB12
